package org.evomaster.core.problem.rest.service

import com.fasterxml.jackson.databind.JsonNode
import com.fasterxml.jackson.databind.ObjectMapper
import com.google.inject.Inject
import com.webfuzzing.commons.faults.DefinedFaultCategory
import org.evomaster.core.EMConfig
import javax.annotation.PostConstruct

import org.evomaster.core.logging.LoggingUtil
import org.evomaster.core.problem.enterprise.DetectedFaultUtils
import org.evomaster.core.problem.enterprise.ExperimentalFaultCategory
import org.evomaster.core.problem.enterprise.SampleType
import org.evomaster.core.problem.enterprise.auth.AuthSettings
import org.evomaster.core.problem.enterprise.auth.NoAuth
import org.evomaster.core.problem.externalservice.HostnameResolutionAction
import org.evomaster.core.problem.httpws.HttpWsCallResult
import org.evomaster.core.problem.httpws.auth.HttpWsAuthenticationInfo
import org.evomaster.core.problem.httpws.auth.HttpWsNoAuth
import org.evomaster.core.problem.rest.*
import org.evomaster.core.problem.rest.builder.CreateResourceUtils
import org.evomaster.core.problem.rest.builder.RestIndividualSelectorUtils
import org.evomaster.core.problem.rest.data.*
import org.evomaster.core.problem.rest.oracle.RestSecurityOracle.Companion.SQLI_PAYLOADS
import org.evomaster.core.problem.rest.oracle.RestSecurityOracle.Companion.XSS_PAYLOADS
import org.evomaster.core.problem.api.param.Param
import org.evomaster.core.problem.rest.param.BodyParam
import org.evomaster.core.problem.rest.param.PathParam
import org.evomaster.core.problem.rest.param.QueryParam
import org.evomaster.core.problem.rest.resource.RestResourceCalls
import org.evomaster.core.problem.rest.service.sampler.AbstractRestSampler
import org.evomaster.core.problem.security.service.SSRFAnalyser
import org.evomaster.core.search.gene.string.StringGene

import org.evomaster.core.search.*
import org.evomaster.core.search.gene.BooleanGene
import org.evomaster.core.search.gene.Gene
import org.evomaster.core.search.gene.ObjectGene
import org.evomaster.core.search.gene.collection.ArrayGene
import org.evomaster.core.search.gene.collection.EnumGene
import org.evomaster.core.search.gene.collection.MapGene
import org.evomaster.core.search.gene.collection.TaintedArrayGene
import org.evomaster.core.search.gene.interfaces.WrapperGene
import org.evomaster.core.search.gene.placeholder.CycleObjectGene
import org.evomaster.core.search.gene.placeholder.LimitObjectGene
import org.evomaster.core.search.gene.numeric.NumberGene
import org.evomaster.core.search.gene.utils.GeneUtils
import org.evomaster.core.search.gene.wrapper.OptionalGene
import org.evomaster.core.search.gene.wrapper.ChoiceGene
import org.evomaster.core.search.gene.wrapper.SelectableWrapperGene
import org.evomaster.core.search.service.Archive
import org.evomaster.core.search.service.FitnessFunction
import org.evomaster.core.search.service.IdMapper
import org.evomaster.core.search.service.Randomness
import org.evomaster.core.search.service.SearchGlobalState
import org.evomaster.core.search.service.time.ExecutionPhaseController
import org.evomaster.core.search.service.time.TimeBoxedPhase
import org.evomaster.core.utils.StackTraceUtils
import org.slf4j.Logger
import org.slf4j.LoggerFactory


/**
 * Service class used to do security testing after the search phase.
 *
 * This class can add new test cases to the archive that, by construction, do reveal a security fault.
 * But, the actual check if a test indeed finds a fault is in [org.evomaster.core.problem.rest.oracle.RestSecurityOracle]
 * called in the fitness function, and not directly here.
 */
class RestSecurityBuilder : TimeBoxedPhase {

    companion object {
        private val log: Logger = LoggerFactory.getLogger(RestSecurityBuilder::class.java)

        private const val MODEL_RESOURCE = "/stateful-authz-model.csv"

        private const val PRIOR = "__prior__"

        private const val MIN_TOKEN_LENGTH = 4

        private const val MAX_FIELD_DEPTH = 3

        private const val MAX_FIELDS = 80

        private const val MAX_ENUM_VALUES = 12

        private val TOKEN_PIECE = Regex("[^A-Za-z0-9]+")

        private val TOKEN_PART = Regex("[A-Z]+(?![a-z])|[A-Z][a-z0-9]*|[a-z0-9]+")

        private fun loadModel(): Map<String, Map<String, Double>> {
            val stream = RestSecurityBuilder::class.java.getResourceAsStream(MODEL_RESOURCE)
            if (stream == null) {
                log.warn("Stateful-authorization model $MODEL_RESOURCE is missing from the classpath:" +
                        " no transition can be inferred and oracle 970 will never be raised")
                return emptyMap()
            }
            val model = mutableMapOf<String, MutableMap<String, Double>>()
            for (line in stream.bufferedReader().readLines()) {
                val row = line.trim().split(",")
                if (row.size != 3) {
                    continue
                }
                val weight = row[2].toDoubleOrNull() ?: continue
                val rows = model.getOrPut(row[0]) { mutableMapOf() }
                rows[row[1]] = weight
            }
            val missing = mutableListOf<String>()
            for (name in listOf("op", "role", "victim")) {
                if (model[name]?.containsKey(PRIOR) != true) {
                    missing.add(name)
                }
            }
            for (name in listOf("low", "high", "lowstr", "highstr")) {
                if (model[name].isNullOrEmpty()) {
                    missing.add(name)
                }
            }
            if (missing.isNotEmpty()) {
                log.warn("Stateful-authorization model $MODEL_RESOURCE carries no usable table $missing:" +
                        " no transition can be inferred and oracle 970 will never be raised")
            }
            return model
        }

        private val MODEL = loadModel()

        private fun table(name: String): Map<String, Double> = MODEL[name] ?: emptyMap()

        fun tokens(text: String, minLength: Int = MIN_TOKEN_LENGTH): Set<String> {
            val out = mutableSetOf<String>()
            for (piece in text.split(TOKEN_PIECE)) {
                if (piece.isEmpty()) {
                    continue
                }
                for (match in TOKEN_PART.findAll(piece)) {
                    val token = match.value.lowercase()
                    if (token.length < minLength || isDigitsOnly(token)) {
                        continue
                    }
                    out.add(token)
                }
            }
            return out
        }

        private fun isDigitsOnly(s: String): Boolean {
            for (c in s) {
                if (c !in '0'..'9') {
                    return false
                }
            }
            return true
        }

        class SchemaField(val loc: String, val name: String, val gene: Gene, val value: Gene) {
            val leaf: String = name.split(".").last().replace("[]", "")
            val parents: List<String> = name.split(".").dropLast(1).map { it.replace("[]", "") }
            val enumValues: List<String>
            val kind: String

            init {
                var enum: EnumGene<*>? = null
                if (value is EnumGene<*>) {
                    enum = value
                } else if (value is ArrayGene<*>) {
                    val inner = valueGene(value.template)
                    if (inner is EnumGene<*>) {
                        enum = inner
                    }
                }
                val names = mutableListOf<String>()
                if (enum != null) {
                    for (v in enum.values) {
                        names.add(v.toString())
                    }
                }
                enumValues = names
                kind = when {
                    value is BooleanGene -> "bool"
                    enum != null && enumValues.isNotEmpty() -> "enum"
                    value is NumberGene<*> -> "num"
                    value is ArrayGene<*> || value is TaintedArrayGene -> "array"
                    value is ObjectGene || value is MapGene<*, *> || value is CycleObjectGene || value is LimitObjectGene -> "object"
                    else -> "str"
                }
            }

            val key: String get() = "$loc:$name"

            fun features(): Set<String> {
                val fs = mutableSetOf("k:$kind", "l:$loc", "w:${leaf.lowercase()}")
                for (t in tokens(leaf)) {
                    fs.add("n:$t")
                }
                for (p in parents) {
                    for (t in tokens(p)) {
                        fs.add("a:$t")
                    }
                }
                for (v in enumValues.take(MAX_ENUM_VALUES)) {
                    for (t in tokens(v)) {
                        fs.add("e:$t")
                    }
                }
                return fs
            }
        }

        private fun valueGene(g: Gene): Gene {
            var cur = g
            while (cur is WrapperGene) {
                val next = if (cur is ChoiceGene<*>) cur.getViewOfChildren().lastOrNull() else cur.getViewOfChildren().firstOrNull()
                cur = next ?: return cur
            }
            return cur
        }

        private fun alternatives(g: Gene): List<Gene> {
            if (g is ChoiceGene<*>) {
                val out = mutableListOf<Gene>()
                for (child in g.getViewOfChildren()) {
                    out.addAll(alternatives(child))
                }
                return out
            }
            if (g is WrapperGene) {
                return alternatives(g.getViewOfChildren().first())
            }
            return listOf(g)
        }

        private fun objectFields(g: Gene): List<Gene> {
            val out = mutableListOf<Gene>()
            val seenNames = mutableSetOf<String>()
            for (alt in alternatives(g)) {
                if (alt !is ObjectGene) {
                    continue
                }
                for (field in alt.fields) {
                    if (field.name in seenNames) {
                        continue
                    }
                    seenNames.add(field.name)
                    out.add(field)
                }
            }
            return out
        }

        private fun walkBody(name: String, g: Gene, depth: Int, out: MutableList<SchemaField>) {
            val v = valueGene(g)
            out.add(SchemaField("body", name, g, v))
            if (depth >= MAX_FIELD_DEPTH) {
                return
            }
            if (v is ArrayGene<*>) {
                for (child in objectFields(v.template)) {
                    walkBody("$name[].${child.name}", child, depth + 1, out)
                }
            } else {
                for (child in objectFields(g)) {
                    walkBody("$name.${child.name}", child, depth + 1, out)
                }
            }
        }

        fun schemaFields(a: RestCallAction): List<SchemaField> {
            val out = mutableListOf<SchemaField>()
            for (p in a.parameters) {
                if (p is PathParam) {
                    out.add(SchemaField("path", p.name, p.primaryGene(), valueGene(p.primaryGene())))
                }
            }
            for (p in a.parameters) {
                if (p is QueryParam) {
                    out.add(SchemaField("query", p.name, p.primaryGene(), valueGene(p.primaryGene())))
                }
            }
            for (p in a.parameters) {
                if (p !is BodyParam) {
                    continue
                }
                val root = valueGene(p.primaryGene())
                val top = if (root is ArrayGene<*>) objectFields(root.template) else objectFields(p.primaryGene())
                for (field in top) {
                    walkBody(field.name, field, 1, out)
                }
            }
            return out.take(MAX_FIELDS)
        }

        fun opFeatures(a: RestCallAction): Set<String> {
            val fs = mutableSetOf("v:${a.verb.name}")
            for (t in tokens(a.path.toString())) {
                fs.add("p:$t")
            }
            for (f in schemaFields(a)) {
                for (t in tokens(f.leaf)) {
                    fs.add("f:$t")
                }
            }
            return fs
        }

        private fun evidence(name: String, features: Set<String>): Double {
            val t = table(name)
            var sum = 0.0
            for (feature in features) {
                sum += t[feature] ?: 0.0
            }
            return sum
        }

        private fun prior(name: String): Double = table(name)[PRIOR] ?: Double.NEGATIVE_INFINITY

        fun fieldScore(name: String, f: SchemaField): Double = prior(name) + evidence(name, f.features())

        private val opEvidenceCache = java.util.concurrent.ConcurrentHashMap<String, Double>()

        fun transitionEvidence(a: RestCallAction): Double =
            opEvidenceCache.getOrPut(a.getName()) { evidence("op", opFeatures(a)) }

        fun transitionScore(a: RestCallAction): Double = prior("op") + transitionEvidence(a)

        fun valueScore(name: String, value: String): Double {
            val v = value.lowercase()
            var best: Double? = null
            for ((key, weight) in table(name)) {
                if (!v.contains(key)) {
                    continue
                }
                if (best == null || weight > best) {
                    best = weight
                }
            }
            return best ?: 0.0
        }

        private val TRANSITION_VERBS =
            listOf(HttpVerb.PUT, HttpVerb.PATCH, HttpVerb.POST, HttpVerb.DELETE)

        private const val MAX_STATEFUL_TRIPLE_ATTEMPTS = 20

        private const val MAX_UNPROVEN_CANDIDATE_ATTEMPTS = 5

        private const val MAX_PRIVILEGE_RESTORES = 3

        fun looksLikePermissionReducingTransition(a: RestCallAction): Boolean {
            if (a.verb !in TRANSITION_VERBS) {
                return false
            }
            return transitionScore(a) > 0.0
        }
    }

    /**
     * Archive including test cases
     */
    @Inject
    private lateinit var archive: Archive<RestIndividual>

    @Inject
    private lateinit var sampler: AbstractRestSampler

    @Inject
    private lateinit var callGraph: CallGraphService

    @Inject
    private lateinit var randomness: Randomness

    @Inject
    private lateinit var fitness: FitnessFunction<RestIndividual>

    @Inject
    private lateinit var idMapper: IdMapper

    @Inject
    private lateinit var builder: RestIndividualBuilder

    @Inject
    private lateinit var config: EMConfig

    @Inject
    private lateinit var ssrfAnalyser: SSRFAnalyser

    @Inject
    protected lateinit var searchGlobalState: SearchGlobalState

    @Inject
    private lateinit var epc: ExecutionPhaseController

    /**
     * All actions that can be defined from the OpenAPI schema
     */
    private lateinit var actionDefinitions: List<RestCallAction>


    /**
     * Individuals in the solution.
     * Derived from archive.
     */
    private lateinit var individualsInSolution: List<EvaluatedIndividual<RestIndividual>>

    private lateinit var authSettings: AuthSettings

    /**
     * Function called after init. This function initializes REST sampler definitions
     * and authentication settings.
     */
    @PostConstruct
    private fun postInit() {

        actionDefinitions = sampler.getActionDefinitions() as List<RestCallAction>

        authSettings = sampler.authentications
    }

    override fun applyPhase() {
        applySecurityPhase()
    }

    override fun hasPhaseTimedOut(): Boolean {
        return epc.hasPhaseTimedOut(ExecutionPhaseController.Phase.SECURITY)
    }

    /**
     * Apply a set rule of generating new test cases, which will be added to the current archive.
     * Extract a new test suite(s) from the archive.
     */
    fun applySecurityPhase(): Solution<RestIndividual> {

        // extract individuals from the archive
        individualsInSolution = this.archive.extractSolution().individuals

        expandWithForbidden()
        //recompute due to possible new tests we might need
        individualsInSolution = this.archive.extractSolution().individuals

        if(!hasPhaseTimedOut()) {
            addForStatefulAccessControl()
        }

        // we can see what is available from the schema, and then check if already existing a test for it in archive
        // newly generated tests will be added back to archive
        if(!hasPhaseTimedOut()) {
            addForAccessControl()
        }

        //TODO this could be applied to GraphQL and RPC, isn't it? if so, should refactor
        //SQLi, XSS, SSRF, etc.
        if(!hasPhaseTimedOut()) {
            addForInjections()
        }

        //eg leaked stack traces
        if(!hasPhaseTimedOut()) {
            addForInfoLeakage()
        }

        // just return the archive for solutions including the security tests.
        return archive.extractSolution()
    }


    /**
     * During the search, we do not explicitly try different users in the same test case.
     * as such, getting tests with 403 might be tricky.
     * but having such tests might be necessary for some types of oracles we designed
     */
    private fun expandWithForbidden() {

        actionDefinitions.forEach { op ->

            if(hasPhaseTimedOut()) return

            val forbidden = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                op.verb,
                op.path,
                status = 403
            )
            if(forbidden.isNotEmpty()){
                //we already have it, so nothing to do
                return@forEach
            }

            val unauthorized = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                op.verb,
                op.path,
                status = 401
            )
            if(unauthorized.isEmpty()){
                //there is no 401, so does not seem auth is applied to this endpoint.
                //note: getting 401 during search should be simple, as we do send requests without
                // auth, given a certain probability
                return@forEach
            }

            val candidates = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                op.verb,
                op.path,
                statusGroup = StatusGroup.G_2xx,
                authenticated = true
            )

            if (candidates.isNotEmpty()){
                handleCandidatesFor403(op.verb, op.path, candidates)
            }
        }
    }

    private fun handleCandidatesFor403(verb: HttpVerb, path: RestPath, candidates: List<EvaluatedIndividual<RestIndividual>>){

        /*
            we have no idea of the access policy for each user.
            for example, an admin will not get any 403.
            so, we need to check each possible user for which we got a 2xx
         */
        candidates.mapNotNull {
            //first make copy and slice off all after the 2xx
            val index = RestIndividualSelectorUtils.findIndexOfAction(
                it,
                verb,
                path,
                statusGroup = StatusGroup.G_2xx,
                authenticated = true
            )
            if (index < 0) {
                //can this ever happen?
                log.warn("Failed to identify authenticated GET action with 2xx")
                null
            } else {
                val copy = RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(it.individual, index)
                copy
            }
        }
            // then, just take 1 test per user
            .distinctBy { it.seeMainExecutableActions().last().auth.name }
            .forEach { ind ->
                //finally, evaluate all of those with a different auth
                val lastCall = ind.seeMainExecutableActions().last()
                val otherUsers = authSettings.getAllOthers(lastCall.auth.name, HttpWsAuthenticationInfo::class.java)

                //try each of them
                otherUsers.forEach { otherAuth ->
                    val copy = ind.copy() as RestIndividual

                    if(lastCall.verb == HttpVerb.PUT){
                        /*
                            a PUT might create the resource, so need to duplicate before changing auth. ie
                            from
                            PUT /x FOO
                            to
                            PUT /x FOO
                            PUT /x BAR
                         */
                        val repeat = lastCall.copy() as RestCallAction
                        repeat.forceNewTaints()
                        repeat.resetLocalIdRecursively()
                        copy.addMainActionInEmptyEnterpriseGroup(action = repeat)
                        copy.doInitializeLocalId()
                    }
                    copy.seeMainExecutableActions().last().auth = otherAuth
                    org.evomaster.core.Lazy.assert {copy.verifyValidity(); true}

                    val ei = fitness.computeWholeAchievedCoverageForPostProcessing(copy)
                    if(ei != null) {
                        archive.addIfNeeded(ei)
                        val res = ei.evaluatedMainActions().last().result as RestCallResult
                        if(res.getStatusCode() == 403){
                            //we are done
                            return
                        }
                    }
                }
            }
    }

    private fun addForAccessControl() {

        /*
            for black-box testing, we can only rely on REST-style guidelines to infer relations between operations
            and resources.
            for white-box, we can rely on what actually accessed in databases.
            however, there can be different kinds of databases (SQL and NoSQL, like Mongo and Neo4J).
            As we might not be able to support all of them (and other resources that are not stored in databases),
            even in white-box testing we still want to consider REST-style
         */

        accessControlBasedOnRESTGuidelines()
        //TODO implement access control based on database monitoring
        //accessControlBasedOnDatabaseMonitoring()
    }

    private fun accessControlBasedOnDatabaseMonitoring() {
        TODO("Not yet implemented")
    }

    private val emptyRoleList = "[]"

    private val numericRoleCandidates = listOf("1", "0", "2")

    private val elevatedNumericRoleCandidates = listOf("0", "1", "2")

    private val privilegeReducedInPhase = mutableSetOf<String>()

    private val privilegeReducedByProof = mutableSetOf<String>()

    private val refusedTransitionVictims = mutableSetOf<Pair<String, String>>()

    private var statefulTripleAttempts = 0

    private var privilegeRestoreAttempts = 0

    private var candidateAttempts = 0
    private var candidateProven = false
    private var candidateIsLast = true

    private var lastSourceCode: Int? = null
    private var lastTransitionCode: Int? = null
    private var transitionNotFoundSeen = false

    private var victimRefused = false

    var statefulTripleUnderEvaluation = false
        private set

    private enum class RoleAttempt { TRIPLE_BUILT, STOP_VICTIM, NEXT }

    private fun candidateCapReached(): Boolean =
        !candidateProven && !candidateIsLast && candidateAttempts >= MAX_UNPROVEN_CANDIDATE_ATTEMPTS

    private fun attemptAllowed(): Boolean =
        statefulTripleAttempts < MAX_STATEFUL_TRIPLE_ATTEMPTS && !candidateCapReached()

    private class TransitionCandidate(val op: RestCallAction, val reducedValues: List<String>)

    private fun addForStatefulAccessControl() {

        if (!config.isEnabledFaultCategory(ExperimentalFaultCategory.SECURITY_STATEFUL_AUTHORIZATION)) {
            log.debug("Skipping experimental stateful-authorization security test as disabled in configuration")
            return
        }
        if (!checkForAtLeastNumberOfAuthenticatedUsers(2)) {
            return
        }

        individualsInSolution = archive.extractSolution().individuals

        if (log.isDebugEnabled) {
            logModelScores()
        }
        val ranked = rankPermissionReducingTransitions()
        if (ranked.isEmpty()) {
            log.debug("Skipping stateful-authorization: no permission-reducing transition endpoint found")
            return
        }
        val viable = mutableListOf<TransitionCandidate>()
        for (candidate in ranked) {
            if (routeLooksMissing(candidate)) {
                log.debug("Stateful-authorization transition candidate ${candidate.getName()}" +
                        " skipped: every call on its path and parent path returned 404")
                continue
            }
            val values = harvestReducedRoleCandidates(candidate)
            val roleField = roleField(candidate)
            log.debug("Stateful-authorization transition candidate ${candidate.getName()}" +
                    " score ${transitionScore(candidate)}" +
                    " roleField ${roleField?.key}" +
                    " victimField ${victimField(candidate, roleField)?.key}" +
                    " reducedRoleValues ${values.size}")
            if (values.isNotEmpty()) {
                viable.add(TransitionCandidate(candidate, values))
            }
        }
        if (viable.isEmpty()) {
            log.debug("Skipping stateful-authorization: no reduced role value could be proposed" +
                    " for any of ${ranked.size} transition candidates")
            return
        }

        for (index in viable.indices) {
            val transitionOp = viable[index].op
            log.debug("Stateful-authorization transition chosen: ${transitionOp.getName()}" +
                    " (candidate ${index + 1} of ${viable.size})")
            log.debug("Stateful-authorization reduced role values: ${viable[index].reducedValues}")
            transitionNotFoundSeen = false
            candidateAttempts = 0
            candidateProven = false
            candidateIsLast = index == viable.lastIndex
            privilegeRestoreAttempts = 0
            privilegeReducedInPhase.retainAll(privilegeReducedByProof)

            var sources = guardedSources(listOf(HttpVerb.PUT, HttpVerb.PATCH), transitionOp)
            if (!anyAuthenticatedSuccess(sources)) {
                sources = guardedSources(listOf(HttpVerb.POST), transitionOp)
            }
            val sourceNames = mutableListOf<String>()
            for (op in sources) {
                sourceNames.add("${op.verb}:${op.path}")
            }
            log.debug("Stateful-authorization guarded source candidates: ${sources.size} $sourceNames")

            var stopSources = false
            for (op in sources) {
                if (hasPhaseTimedOut()) {
                    log.debug("Stateful-authorization: phase timed out before source ${op.verb}:${op.path}")
                    return
                }

                val victimCandidates = victimSlicesOn(op)
                val victimNames = mutableListOf<String>()
                for (slice in victimCandidates) {
                    victimNames.add(slice.seeMainExecutableActions().last().auth.name)
                }
                log.debug("Stateful-authorization source ${op.verb}:${op.path} victims $victimNames")

                for (victimSlice in victimCandidates) {
                    if (hasPhaseTimedOut()) {
                        log.debug("Stateful-authorization: phase timed out on source ${op.verb}:${op.path}")
                        return
                    }
                    if (statefulTripleAttempts >= MAX_STATEFUL_TRIPLE_ATTEMPTS) {
                        log.debug("Stateful-authorization: attempt cap $MAX_STATEFUL_TRIPLE_ATTEMPTS reached")
                        return
                    }
                    if (candidateCapReached()) {
                        stopSources = true
                        break
                    }
                    if (buildStatefulAuthzTriple(victimSlice, transitionOp)) {
                        break
                    }
                    if (transitionNotFoundSeen) {
                        stopSources = true
                        break
                    }
                }
                if (stopSources) {
                    break
                }
            }
            if (statefulTripleAttempts >= MAX_STATEFUL_TRIPLE_ATTEMPTS) {
                log.debug("Stateful-authorization: attempt cap $MAX_STATEFUL_TRIPLE_ATTEMPTS reached")
                return
            }
            if (candidateCapReached()) {
                LoggingUtil.getInfoLogger().info(
                    "Stateful-authorization transition ${transitionOp.getName()} not proven after" +
                        " $candidateAttempts attempts; trying the next candidate"
                )
            } else if (transitionNotFoundSeen) {
                log.debug("Stateful-authorization transition ${transitionOp.getName()} returned 404 after a 2xx source;" +
                        " trying the next candidate")
            } else {
                log.debug("Stateful-authorization transition ${transitionOp.getName()} exhausted its sources after" +
                        " $candidateAttempts attempts, proven $candidateProven")
            }
        }
        log.debug("Stateful-authorization: sources exhausted after $statefulTripleAttempts triple attempts")
    }

    private fun guardedSources(verbs: List<HttpVerb>, transitionOp: RestCallAction): List<RestCallAction> {
        val out = mutableListOf<RestCallAction>()
        for (verb in verbs) {
            for (op in RestIndividualSelectorUtils.getAllActionDefinitions(actionDefinitions, verb)) {
                if (op.path == transitionOp.path) {
                    continue
                }
                val denied = RestIndividualSelectorUtils.findIndividuals(
                    individualsInSolution, verb, op.path, status = 403
                )
                if (denied.isNotEmpty()) {
                    out.add(op)
                }
            }
        }

        return out
    }

    private fun anyAuthenticatedSuccess(ops: List<RestCallAction>): Boolean {
        for (op in ops) {
            val allowed = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution, op.verb, op.path,
                statusGroup = StatusGroup.G_2xx, authenticated = true
            )
            if (allowed.isNotEmpty()) {
                return true
            }
        }
        return false
    }

    private fun victimSlicesOn(source: RestCallAction): List<RestIndividual> {
        val slices = RestIndividualSelectorUtils.findAndSlice(
            individualsInSolution, source.verb, source.path,
            statusGroup = StatusGroup.G_2xx, authenticated = true
        ).sortedBy { it.size() }
        val out = mutableListOf<RestIndividual>()
        val seenUsers = mutableSetOf<String>()
        for (slice in slices) {
            val user = slice.seeMainExecutableActions().last().auth.name
            if (user in seenUsers) {
                continue
            }
            seenUsers.add(user)
            out.add(slice)
        }
        return out
    }

    private fun operatorsFor(
        victimAuth: HttpWsAuthenticationInfo,
        transitionDef: RestCallAction
    ): List<HttpWsAuthenticationInfo> {
        val ranTransition = mutableListOf<HttpWsAuthenticationInfo>()
        val others = mutableListOf<HttpWsAuthenticationInfo>()
        for (o in authSettings.getAllOthers(victimAuth.name, HttpWsAuthenticationInfo::class.java)) {
            if (privilegeReducedInPhase.contains(o.name)) {
                continue
            }
            val allowed = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution, transitionDef.verb, transitionDef.path,
                statusGroup = StatusGroup.G_2xx, authenticatedWith = o.name
            )
            if (allowed.isNotEmpty()) {
                ranTransition.add(o)
            } else {
                others.add(o)
            }
        }
        return ranTransition + others
    }

    private fun buildStatefulAuthzTriple(
        victimSlice: RestIndividual,
        transitionDef: RestCallAction
    ): Boolean {
        val victimAuth = victimSlice.seeMainExecutableActions().lastOrNull()?.auth ?: return false
        if (victimAuth is NoAuth) return false

        val pair = transitionDef.getName() to victimAuth.name
        if (refusedTransitionVictims.contains(pair)) {
            log.debug("Stateful-authorization: ${transitionDef.getName()} already refused victim '${victimAuth.name}'")
            return false
        }

        if (privilegeReducedInPhase.contains(victimAuth.name)) {
            log.debug("Stateful-authorization: victim '${victimAuth.name}' already reduced in this phase")
            return false
        }

        val operators = operatorsFor(victimAuth, transitionDef)
        val operatorNames = mutableListOf<String>()
        for (o in operators) {
            operatorNames.add(o.name)
        }
        log.debug("Stateful-authorization victim '${victimAuth.name}' operators $operatorNames")

        val field = roleField(transitionDef)
        var current: List<String> = emptyList()
        var roleValues: List<String> = emptyList()
        if (field != null) {
            current = victimRoleValues(victimAuth, transitionDef, field)
            roleValues = reducedRoleValues(field, current)
        }
        log.debug("Stateful-authorization victim '${victimAuth.name}' current roles $current, reduced role values $roleValues")

        victimRefused = false

        for (operator in operators) {
            val outcome = tryReducedRoles(victimSlice, transitionDef, roleValues, operator, victimAuth, pair)
            if (outcome == RoleAttempt.TRIPLE_BUILT) {
                return true
            }
            if (outcome == RoleAttempt.STOP_VICTIM) {
                return false
            }
        }

        val src = lastSourceCode
        val operatorsRefused = lastTransitionCode == 401 || lastTransitionCode == 403
        if (operatorsRefused && src != null && StatusGroup.G_2xx.isInGroup(src)) {
            val outcome = restoreOperatorsAndRetry(victimSlice, transitionDef, roleValues, operators, victimAuth, pair)
            if (outcome == RoleAttempt.TRIPLE_BUILT) {
                return true
            }
            if (outcome == RoleAttempt.STOP_VICTIM) {
                return false
            }
        }

        if (victimRefused) {
            refusedTransitionVictims.add(pair)
            LoggingUtil.getInfoLogger().info(
                "Stateful-authorization: ${transitionDef.getName()} refused or rejected every attempt on victim" +
                    " '${victimAuth.name}'; that victim is skipped for this transition"
            )
        }
        return false
    }

    private fun tryReducedRoles(
        victimSlice: RestIndividual,
        transitionDef: RestCallAction,
        roleValues: List<String>,
        operator: HttpWsAuthenticationInfo,
        victimAuth: HttpWsAuthenticationInfo,
        pair: Pair<String, String>
    ): RoleAttempt {
        for (reducedRole in roleValues) {
            if (hasPhaseTimedOut()) return RoleAttempt.STOP_VICTIM
            if (!attemptAllowed()) return RoleAttempt.STOP_VICTIM

            val before = statefulTripleAttempts
            if (executeStatefulAuthzTriple(victimSlice, transitionDef, reducedRole, operator)) {
                return RoleAttempt.TRIPLE_BUILT
            }
            if (statefulTripleAttempts == before) {
                continue
            }
            if (lastSourceCode == null) {
                noStatusRecorded(transitionDef, victimAuth.name, operator.name)
                return RoleAttempt.STOP_VICTIM
            }
            if (transitionRefusedAfterSource()) {
                victimRefused = true
            }
            if (privilegeReducedInPhase.contains(victimAuth.name) || refusedTransitionVictims.contains(pair)) {
                return RoleAttempt.STOP_VICTIM
            }
            if (!transitionRejectedRoleValue()) {
                return RoleAttempt.NEXT
            }
        }
        return RoleAttempt.NEXT
    }

    private fun restoreOperatorsAndRetry(
        victimSlice: RestIndividual,
        transitionDef: RestCallAction,
        roleValues: List<String>,
        operators: List<HttpWsAuthenticationInfo>,
        victimAuth: HttpWsAuthenticationInfo,
        pair: Pair<String, String>
    ): RoleAttempt {
        val exclude = roleValues.firstOrNull() ?: ""
        val plans = mutableMapOf<String, List<List<Pair<String, String>>>>()
        var anyPlan = false
        for (operator in operators) {
            val operatorPlans = restorePlans(transitionDef, operator, exclude)
            plans[operator.name] = operatorPlans
            if (operatorPlans.isNotEmpty()) {
                anyPlan = true
            }
        }
        if (!anyPlan) {
            LoggingUtil.getInfoLogger().info(
                "Stateful-authorization restore unavailable on ${transitionDef.getName()}:" +
                    " no elevated role value for the operators of victim '${victimAuth.name}'"
            )
        }

        for (operator in operators) {
            for (plan in plans[operator.name] ?: emptyList()) {
                if (hasPhaseTimedOut()) return RoleAttempt.STOP_VICTIM
                if (!attemptAllowed()) return RoleAttempt.STOP_VICTIM
                if (privilegeRestoreAttempts >= MAX_PRIVILEGE_RESTORES) {
                    LoggingUtil.getInfoLogger().info(
                        "Stateful-authorization restore budget of $MAX_PRIVILEGE_RESTORES spent on" +
                            " ${transitionDef.getName()}"
                    )
                    return RoleAttempt.NEXT
                }

                if (!restorePrivilege(transitionDef, victimAuth, operator, plan, victimSlice)) {
                    continue
                }

                val outcome = tryReducedRoles(victimSlice, transitionDef, roleValues, operator, victimAuth, pair)
                if (outcome == RoleAttempt.TRIPLE_BUILT || outcome == RoleAttempt.STOP_VICTIM) {
                    return outcome
                }
            }
        }
        return RoleAttempt.NEXT
    }

    private fun noStatusRecorded(transitionDef: RestCallAction, victim: String, operator: String) {
        LoggingUtil.getInfoLogger().warn(
            "Stateful-authorization attempt on ${transitionDef.getName()} recorded no status code" +
                " (victim '$victim', operator '$operator'); trying the next victim or source"
        )
    }

    private fun transitionRefusedAfterSource(): Boolean {
        val src = lastSourceCode ?: return false
        val code = lastTransitionCode ?: return false
        return StatusGroup.G_2xx.isInGroup(src) && (code == 401 || code == 403 || transitionRejectedRoleValue())
    }

    private fun transitionRejectedRoleValue(): Boolean {
        val code = lastTransitionCode ?: return false
        return code in 400..599 && code !in setOf(401, 403, 404)
    }

    private fun statusIn(ei: EvaluatedIndividual<RestIndividual>, a: RestCallAction): Int? {
        val result = ei.seeResult(a.getLocalId())
        if (result is RestCallResult) {
            return result.getStatusCode()
        }
        return null
    }

    private fun executeStatefulAuthzTriple(
        victimSlice: RestIndividual,
        transitionDef: RestCallAction,
        reducedRole: String,
        operator: HttpWsAuthenticationInfo
    ): Boolean {
        val base = victimSlice.copy() as RestIndividual
        val source = base.seeMainExecutableActions().lastOrNull() ?: return false
        val victimAuth = source.auth
        if (victimAuth is NoAuth) return false

        val transition = transitionDef.copy() as RestCallAction
        transition.resetLocalIdRecursively()
        transition.forceNewTaints()
        transition.doInitialize(randomness)
        transition.auth = operator
        val targeted = setUserTargetToVictim(transition, victimAuth)
        if (targeted == null) {
            log.debug("Stateful-authorization: could not target victim '${victimAuth.name}' on ${transition.getName()}")
            return false
        }
        val reduced = setRoleFieldToReduced(transition, reducedRole)
        if (reduced == null) {
            log.debug("Stateful-authorization: could not set reduced role '$reducedRole' on ${transition.getName()}")
            return false
        }
        keepOnlyTargetFields(transition, (targeted + reduced).toSet())
        setUserNameFieldsToVictim(transition, victimAuth, targeted)
        base.addMainActionInEmptyEnterpriseGroup(action = transition)

        val followUp = source.copy() as RestCallAction
        followUp.resetLocalIdRecursively()
        followUp.forceNewTaints()
        followUp.auth = victimAuth
        followUp.usePreviousLocationId = source.usePreviousLocationId
        followUp.bindBasedOn(source.path, source.parameters.filterIsInstance<PathParam>(), null)
        base.addMainActionInEmptyEnterpriseGroup(action = followUp)

        base.doInitializeLocalId()
        base.modifySampleType(SampleType.SECURITY)
        base.ensureFlattenedStructure()
        base.fixResourceForwardLinks()
        org.evomaster.core.Lazy.assert { base.verifyValidity(); true }

        statefulTripleUnderEvaluation = true
        val ei = try {
            fitness.computeWholeAchievedCoverageForPostProcessing(base)
        } finally {
            statefulTripleUnderEvaluation = false
        }
        if (ei == null) {
            log.warn("Failed to evaluate constructed stateful-authorization individual")
            return false
        }
        statefulTripleAttempts++
        candidateAttempts++

        val sourceCode = statusIn(ei, source)
        val transitionCode = statusIn(ei, transition)
        val followUpCode = statusIn(ei, followUp)
        lastSourceCode = sourceCode
        lastTransitionCode = transitionCode
        val sourceAllowed = sourceCode != null && StatusGroup.G_2xx.isInGroup(sourceCode)
        val transitionAllowed = transitionCode != null && StatusGroup.G_2xx.isInGroup(transitionCode)

        if (transitionCode == 404 && sourceAllowed) {
            if (candidateProven) {
                refusedTransitionVictims.add(transitionDef.getName() to victimAuth.name)
                LoggingUtil.getInfoLogger().info(
                    "Stateful-authorization: proven transition ${transitionDef.getName()} returned 404 for victim" +
                        " '${victimAuth.name}'; that victim is skipped for this transition"
                )
            } else {
                transitionNotFoundSeen = true
            }
        }
        val observed = "${sourceCode ?: "-"}/${transitionCode ?: "-"}/${followUpCode ?: "-"}"

        if (transitionAllowed) {
            privilegeReducedInPhase.add(victimAuth.name)
        }

        if (!sourceAllowed || !transitionAllowed || followUpCode == null || followUpCode == 401) {
            val revoked = followUpCode == 401 && sourceAllowed && transitionAllowed
            LoggingUtil.getInfoLogger().info(
                "Discarded a VOID stateful-authorization (MR-A1) attempt on ${source.getName()}" +
                    " (victim '${victimAuth.name}', operator '${operator.name}', codes $observed)" +
                    (if (revoked) " REVOKED: the old victim credential was rejected after the transition" else "")
            )
            return false
        }

        if (StatusGroup.G_2xx.isInGroup(followUpCode) && !reLoginProbeConfirmsPrivilegeRemoved(victimSlice)) {
            LoggingUtil.getInfoLogger().info(
                "Discarded an UNCONFIRMED stateful-authorization (MR-A1) attempt on ${source.getName()}:" +
                    " re-logging the victim in did not show the privilege removed" +
                    " (victim '${victimAuth.name}', operator '${operator.name}', codes $observed)"
            )
            return false
        }

        LoggingUtil.getInfoLogger().info(
            "Assembled a stateful-authorization (MR-A1) triple on ${source.getName()}" +
                " (victim '${victimAuth.name}', operator '${operator.name}'," +
                " transition ${transition.getName()}, statuses $observed)"
        )
        if (followUpCode == 403 || StatusGroup.G_2xx.isInGroup(followUpCode)) {
            if (!candidateProven) {
                LoggingUtil.getInfoLogger().info(
                    "Stateful-authorization transition ${transitionDef.getName()} proven by an attempt with" +
                        " statuses $observed"
                )
            }
            candidateProven = true
            privilegeReducedByProof.add(victimAuth.name)
        }
        if (ExperimentalFaultCategory.SECURITY_STATEFUL_AUTHORIZATION in DetectedFaultUtils.getDetectedFaultCategories(ei)) {
            LoggingUtil.getInfoLogger().info(
                "Constructed a stateful-authorization (MR-A1) test revealing privilege persistence" +
                    " after a role downgrade on ${source.getName()} (victim '${victimAuth.name}')"
            )
        }
        archive.addIfNeeded(ei)
        return true
    }

    private fun lastRecordedStatus(individual: RestIndividual, ei: EvaluatedIndividual<RestIndividual>): Int? {
        var last: Int? = null
        for (a in individual.seeMainExecutableActions()) {
            val code = statusIn(ei, a)
            if (code != null) {
                last = code
            }
        }
        return last
    }

    private fun reLoginProbeConfirmsPrivilegeRemoved(victimSlice: RestIndividual): Boolean {

        val probe = victimSlice.copy() as RestIndividual
        probe.modifySampleType(SampleType.SECURITY)
        val ei = fitness.computeWholeAchievedCoverageForPostProcessing(probe)
            ?: return reLoginProbeInconclusive("the probe could not be evaluated")

        val lastObserved = lastRecordedStatus(probe, ei)
            ?: return reLoginProbeInconclusive("no call of the replayed slice recorded a status code")

        if (lastObserved != 403) {
            return false
        }

        val control = victimSlice.copy() as RestIndividual
        control.modifySampleType(SampleType.SECURITY)
        for (a in control.seeMainExecutableActions()) {
            a.auth = HttpWsNoAuth()
        }
        val cei = fitness.computeWholeAchievedCoverageForPostProcessing(control)
            ?: return reLoginProbeInconclusive("the replayed slice sent without credentials could not be evaluated")
        val anonymousCode = lastRecordedStatus(control, cei)
        LoggingUtil.getInfoLogger().info(
            "Stateful-authorization anonymous control: ${control.seeMainExecutableActions().lastOrNull()?.getName()}" +
                "=${anonymousCode ?: "-"}"
        )
        if (anonymousCode == null) {
            return reLoginProbeInconclusive("no call of the replayed slice sent without credentials recorded a status code")
        }
        if (anonymousCode == 403) {
            return reLoginProbeInconclusive("the replayed slice sent without credentials also ended in 403")
        }
        return true
    }

    private fun reLoginProbeInconclusive(reason: String): Boolean {
        LoggingUtil.getInfoLogger().info("Stateful-authorization re-login probe INCONCLUSIVE: $reason")
        return false
    }

    private fun rankPermissionReducingTransitions(): List<RestCallAction> {
        val transitions = mutableListOf<RestCallAction>()
        for (a in actionDefinitions) {
            if (a.verb in TRANSITION_VERBS && transitionScore(a) > 0.0) {
                transitions.add(a)
            }
        }
        return transitions.sortedByDescending { transitionScore(it) }
    }

    private fun logModelScores() {
        log.debug("Stateful-authorization model tables: op ${table("op").size - 1}" +
                " role ${table("role").size - 1} victim ${table("victim").size - 1}" +
                " low ${table("low").size} high ${table("high").size}")
    }

    private fun roleField(a: RestCallAction): SchemaField? {
        var best: SchemaField? = null
        var bestScore = 0.0
        for (f in schemaFields(a)) {
            if (f.loc == "path") {
                continue
            }
            val score = fieldScore("role", f)
            if (score > 0.0 && (best == null || score > bestScore)) {
                best = f
                bestScore = score
            }
        }
        return best
    }

    private fun victimField(a: RestCallAction, role: SchemaField?): SchemaField? {
        var best: SchemaField? = null
        var bestScore = 0.0
        for (f in schemaFields(a)) {
            if (f.kind != "str" && f.kind != "num") {
                continue
            }
            if (f.key == role?.key) {
                continue
            }
            val score = fieldScore("victim", f)
            if (best == null || score > bestScore) {
                best = f
                bestScore = score
            }
        }
        return best
    }

    private fun tableValues(name: String): List<String> {
        val values = mutableListOf<String>()
        for (entry in table(name).entries.sortedByDescending { it.value }) {
            values.add(entry.key)
        }
        return values
    }

    private fun lowMinusHigh(value: String): Double = valueScore("low", value) - valueScore("high", value)

    private fun reducedRoleValues(field: SchemaField, current: List<String>): List<String> {
        val raw = when (field.kind) {
            "enum" -> {
                val low = mutableListOf<String>()
                val rest = mutableListOf<String>()
                for (v in field.enumValues) {
                    if (lowMinusHigh(v) > 0.0) {
                        low.add(v)
                    } else {
                        rest.add(v)
                    }
                }
                low.sortedByDescending { lowMinusHigh(it) } + rest.sortedByDescending { lowMinusHigh(it) }
            }
            "bool" -> when (current.firstOrNull()?.lowercase()) {
                "true" -> listOf("false")
                "false" -> listOf("true")
                else -> listOf("false")
            }
            "array" -> listOf(emptyRoleList)
            "num" -> numericRoleCandidates
            "str" -> tableValues("lowstr")
            else -> emptyList()
        }
        val held = mutableListOf<String>()
        for (c in current) {
            if (lowMinusHigh(c) <= 0.0) {
                held.add(c)
            }
        }
        val out = mutableListOf<String>()
        for (v in raw) {
            var alreadyHeld = false
            for (h in held) {
                if (h.equals(v, ignoreCase = true)) {
                    alreadyHeld = true
                }
            }
            if (alreadyHeld || v in out) {
                continue
            }
            out.add(v)
        }
        return out
    }

    private fun harvestReducedRoleCandidates(transition: RestCallAction): List<String> {
        val field = roleField(transition) ?: return emptyList()
        return reducedRoleValues(field, emptyList())
    }

    private fun restoreFields(transition: RestCallAction): List<SchemaField> {
        val out = mutableListOf<SchemaField>()
        for (f in schemaFields(transition)) {
            if (f.loc != "path" && fieldScore("role", f) > 0.0) {
                out.add(f)
            }
        }
        return out
    }

    private fun restoreValues(field: SchemaField, snapshot: String?, exclude: String): List<String> {
        if (snapshot != null && valueScore("low", snapshot) <= valueScore("high", snapshot)) {
            return if (snapshot == exclude) emptyList() else listOf(snapshot)
        }
        val raw = when (field.kind) {
            "enum" -> {
                val ranked = field.enumValues.sortedByDescending { valueScore("high", it) - valueScore("low", it) }
                val high = mutableListOf<String>()
                for (v in ranked) {
                    if (valueScore("high", v) > valueScore("low", v)) {
                        high.add(v)
                    }
                }
                if (high.isNotEmpty()) high else ranked
            }
            "bool" -> listOf("true")
            "num" -> elevatedNumericRoleCandidates
            "str" -> tableValues("highstr")
            else -> emptyList()
        }
        val out = mutableListOf<String>()
        for (v in raw) {
            if (v != exclude && v !in out) {
                out.add(v)
            }
        }
        return out
    }

    private fun restorePlans(
        transition: RestCallAction,
        account: HttpWsAuthenticationInfo,
        exclude: String
    ): List<List<Pair<String, String>>> {
        val fields = restoreFields(transition)
        if (fields.isEmpty()) return emptyList()
        val snapshot = victimSnapshot(account, transition, fields)
        val perField = mutableListOf<Pair<String, List<String>>>()
        for (f in fields) {
            val values = restoreValues(f, snapshot[f.key], exclude)
            if (values.isNotEmpty()) {
                perField.add(f.key to values)
            }
        }
        if (perField.isEmpty()) return emptyList()
        var longest = 0
        for (entry in perField) {
            if (entry.second.size > longest) {
                longest = entry.second.size
            }
        }
        val rounds = minOf(longest, MAX_PRIVILEGE_RESTORES)
        val plans = mutableListOf<List<Pair<String, String>>>()
        for (j in 0 until rounds) {
            val plan = mutableListOf<Pair<String, String>>()
            for (entry in perField) {
                val values = entry.second
                plan.add(entry.first to values[minOf(j, values.size - 1)])
            }
            plans.add(plan)
        }
        return plans
    }

    private fun restorePrivilege(
        transitionDef: RestCallAction,
        restorer: HttpWsAuthenticationInfo,
        target: HttpWsAuthenticationInfo,
        plan: List<Pair<String, String>>,
        victimSlice: RestIndividual
    ): Boolean {

        if (privilegeRestoreAttempts >= MAX_PRIVILEGE_RESTORES) return false

        val action = transitionDef.copy() as RestCallAction
        action.resetLocalIdRecursively()
        action.forceNewTaints()
        action.doInitialize(randomness)
        action.auth = restorer
        val targeted = setUserTargetToVictim(action, target)
            ?: return restoreSkipped(action, target.name, "the account could not be placed in the call")
        val byKey = mutableMapOf<String, SchemaField>()
        for (f in schemaFields(action)) {
            byKey[f.key] = f
        }
        val setKeys = mutableListOf<String>()
        val planValues = mutableListOf<String>()
        for (entry in plan) {
            planValues.add(entry.second)
            val f = byKey[entry.first] ?: continue
            if (setField(f, entry.second)) {
                setKeys.add(entry.first)
            }
        }
        if (setKeys.isEmpty()) {
            return restoreSkipped(action, target.name, "no role field accepted the restore values $planValues")
        }
        keepOnlyTargetFields(action, (targeted + setKeys).toSet())
        setUserNameFieldsToVictim(action, target, targeted)

        val base = victimSlice.copy() as RestIndividual
        base.addMainActionInEmptyEnterpriseGroup(action = action)
        base.doInitializeLocalId()
        base.modifySampleType(SampleType.SECURITY)
        base.ensureFlattenedStructure()
        base.fixResourceForwardLinks()

        val ei = fitness.computeWholeAchievedCoverageForPostProcessing(base)
            ?: return restoreSkipped(action, target.name, "the call could not be evaluated")
        privilegeRestoreAttempts++

        val code = statusIn(ei, action)
        val accepted = code != null && StatusGroup.G_2xx.isInGroup(code)
        LoggingUtil.getInfoLogger().info(
            "Privilege-restore ${if (accepted) "accepted" else "refused"} for \'${target.name}\'" +
                " by \'${restorer.name}\' with role \'${planValues.joinToString(",")}\' on ${action.getName()} -> ${code ?: "-"}"
        )
        if (accepted) {
            privilegeReducedInPhase.remove(target.name)
            privilegeReducedByProof.remove(target.name)
            refusedTransitionVictims.clear()
        }
        return accepted
    }

    private fun restoreSkipped(action: RestCallAction, target: String, reason: String): Boolean {
        LoggingUtil.getInfoLogger().info(
            "Stateful-authorization restore skipped for '$target' on ${action.getName()}: $reason"
        )
        return false
    }

    private fun normalize(s: String): String = s.lowercase().filter { it.isLetterOrDigit() }

    private fun setField(f: SchemaField, value: String): Boolean {
        if (!trySetFromStringValue(f.value, value)) return false
        activateAncestors(f.value)
        return true
    }

    private fun activateAncestors(g: Gene) {
        var child: Gene = g
        var p = g.parent
        while (p is Gene) {
            when (p) {
                is SelectableWrapperGene -> p.isActive = true
                is ChoiceGene<*> -> p.selectActiveGene(p.getViewOfChildren().indexOf(child))
            }
            child = p
            p = p.parent
        }
    }

    @Suppress("UNCHECKED_CAST")
    private fun clearArray(f: SchemaField): Boolean {
        val array = (f.value as? ArrayGene<Gene>) ?: return false
        if ((array.minSize ?: 0) != 0) return false
        for (element in array.getViewOfElements()) {
            array.removeExistingElement(element)
        }
        activateAncestors(array)
        return true
    }

    private fun loginKeys(victimAuth: HttpWsAuthenticationInfo): Set<String> {
        val payload = victimAuth.endpointCallLogin?.call?.payload ?: return emptySet()
        val name = victimAuth.name
        val keys = mutableSetOf<String>()
        try {
            val node = ObjectMapper().readTree(payload)
            if (node != null && node.isObject) {
                for (entry in node.fields()) {
                    if (entry.value.isTextual && entry.value.asText() == name) {
                        keys.add(entry.key)
                    }
                }
                if (keys.isNotEmpty()) return keys
            }
        } catch (e: Exception) {
        }
        for (pair in payload.split("&")) {
            val kv = pair.split("=", limit = 2)
            if (kv.size == 2) {
                val v = try { java.net.URLDecoder.decode(kv[1], "UTF-8") } catch (e: Exception) { kv[1] }
                if (v == name) keys.add(kv[0])
            }
        }
        return keys
    }

    private fun identityKeys(victimAuth: HttpWsAuthenticationInfo, victimLeaf: String): Set<String> {
        val keys = mutableSetOf<String>()
        for (k in loginKeys(victimAuth)) {
            keys.add(normalize(k))
        }
        if (victimLeaf.isNotBlank()) keys.add(normalize(victimLeaf))
        return keys
    }

    private data class ScoredObject(val verb: HttpVerb, val path: String, val node: JsonNode, val matches: Int)

    private val victimObjectCache = mutableMapOf<String, List<ScoredObject>>()

    private fun victimObjects(
        victimAuth: HttpWsAuthenticationInfo,
        victimLeaf: String,
        transition: RestCallAction
    ): List<ScoredObject> {
        val cacheKey = "${victimAuth.name}|$victimLeaf|${transition.path}"
        val cached = victimObjectCache[cacheKey]
        if (cached != null) {
            return cached
        }
        val objects = findVictimObjects(victimAuth, victimLeaf, transition)
        victimObjectCache[cacheKey] = objects
        return objects
    }

    private fun findVictimObjects(
        victimAuth: HttpWsAuthenticationInfo,
        victimLeaf: String,
        transition: RestCallAction
    ): List<ScoredObject> {
        val idKeys = identityKeys(victimAuth, victimLeaf)
        if (idKeys.isEmpty()) return emptyList()
        val mapper = ObjectMapper()
        val prefix = transition.path.toString().substringBefore("{")
        val objects = mutableListOf<ScoredObject>()
        for (ea in RestIndividualSelectorUtils.findEvaluatedActions(
            individualsInSolution, statusGroup = StatusGroup.G_2xx
        )) {
            val action = ea.action
            val result = ea.result
            if (action !is RestCallAction || result !is RestCallResult) continue
            val body = result.getBody() ?: continue
            if (!body.contains(victimAuth.name)) continue
            val node = try { mapper.readTree(body) } catch (e: Exception) { continue }
            val found = mutableListOf<JsonNode>()
            collectVictimObjects(node, victimAuth.name, idKeys, found)
            for (o in found) {
                objects.add(ScoredObject(action.verb, action.path.toString(), o, matchingKeys(o, victimAuth.name, idKeys)))
            }
        }
        return objects.sortedWith(Comparator { a, b -> compareVictimObjects(a, b, prefix) })
    }

    private fun compareVictimObjects(a: ScoredObject, b: ScoredObject, prefix: String): Int {
        val aUnderPrefix = prefix.isNotEmpty() && a.path.startsWith(prefix)
        val bUnderPrefix = prefix.isNotEmpty() && b.path.startsWith(prefix)
        if (aUnderPrefix != bUnderPrefix) {
            return if (aUnderPrefix) -1 else 1
        }
        val aGet = a.verb == HttpVerb.GET
        val bGet = b.verb == HttpVerb.GET
        if (aGet != bGet) {
            return if (aGet) -1 else 1
        }
        return b.matches.compareTo(a.matches)
    }

    private fun matchingKeys(node: JsonNode, victimName: String, idKeys: Set<String>): Int {
        var count = 0
        for (entry in node.fields()) {
            val v = entry.value
            if (normalize(entry.key) in idKeys && v.isTextual && v.asText().equals(victimName, ignoreCase = true)) {
                count++
            }
        }
        return count
    }

    private fun collectVictimObjects(
        node: JsonNode,
        victimName: String,
        idKeys: Set<String>,
        into: MutableList<JsonNode>
    ) {
        if (node.isObject && matchingKeys(node, victimName, idKeys) > 0) {
            into.add(node)
        }
        if (node.isContainerNode) {
            for (child in node) {
                collectVictimObjects(child, victimName, idKeys, into)
            }
        }
    }

    private fun objectValue(objects: List<ScoredObject>, normKey: String): String? {
        for (o in objects) {
            var v: JsonNode? = null
            for (entry in o.node.fields()) {
                if (normalize(entry.key) == normKey) {
                    v = entry.value
                    break
                }
            }
            if (v != null && v.isValueNode && !v.isNull) return v.asText()
        }
        return null
    }

    private fun victimId(objects: List<ScoredObject>, normLeaf: String): String? =
        objectValue(objects, normLeaf) ?: objectValue(objects, "id")

    private fun hasIdToken(leaf: String): Boolean {
        val t = tokens(leaf, 1)
        return "id" in t || "ids" in t
    }

    private fun getObjects(objects: List<ScoredObject>): List<ScoredObject> {
        val out = mutableListOf<ScoredObject>()
        for (o in objects) {
            if (o.verb == HttpVerb.GET) {
                out.add(o)
            }
        }
        return out
    }

    private fun victimSnapshot(
        victimAuth: HttpWsAuthenticationInfo,
        transition: RestCallAction,
        fields: List<SchemaField>
    ): Map<String, String> {
        val vfLeaf = victimField(transition, roleField(transition))?.leaf ?: ""
        val objects = getObjects(victimObjects(victimAuth, vfLeaf, transition))
        val snapshot = mutableMapOf<String, String>()
        for (f in fields) {
            val v = objectValue(objects, normalize(f.leaf))
            if (v != null) {
                snapshot[f.key] = v
            }
        }
        return snapshot
    }

    private fun victimRoleValues(
        victimAuth: HttpWsAuthenticationInfo,
        transition: RestCallAction,
        role: SchemaField
    ): List<String> {
        val vfLeaf = victimField(transition, role)?.leaf ?: ""
        val leaf = normalize(role.leaf)
        val out = mutableListOf<String>()
        for (o in getObjects(victimObjects(victimAuth, vfLeaf, transition))) {
            for (s in scalarsForRoleKey(o.node, leaf)) {
                if (s.isNotBlank() && s !in out) {
                    out.add(s)
                }
            }
        }
        return out
    }

    private fun scalarsForRoleKey(node: JsonNode, leaf: String): List<String> {
        val out = mutableListOf<String>()
        for (entry in node.fields()) {
            val nk = normalize(entry.key)
            if (nk != leaf && !leaf.startsWith(nk)) {
                continue
            }
            val v = entry.value
            if (v.isValueNode && !v.isNull) {
                out.add(v.asText())
            } else if (v.isObject || v.isArray) {
                for (c in v) {
                    if (c.isValueNode && !c.isNull) out.add(c.asText())
                }
            }
        }
        return out
    }

    private fun setUserTargetToVictim(action: RestCallAction, victimAuth: HttpWsAuthenticationInfo): List<String>? {
        val vf = victimField(action, roleField(action)) ?: return null
        val objects = victimObjects(victimAuth, vf.leaf, action)
        if (!placeVictimValue(vf, victimAuth.name, objects)) {
            return null
        }
        val set = mutableListOf(vf.key)
        if (vf.loc != "path") {
            var pathField: SchemaField? = null
            var pathScore = 0.0
            for (f in schemaFields(action)) {
                if (f.loc != "path") {
                    continue
                }
                val score = fieldScore("victim", f)
                if (score > 0.0 && (pathField == null || score > pathScore)) {
                    pathField = f
                    pathScore = score
                }
            }
            if (pathField != null) {
                val id = victimId(objects, normalize(pathField.leaf))
                if (id != null && setField(pathField, id)) set.add(pathField.key)
            }
        }
        return set
    }

    private fun placeVictimValue(f: SchemaField, victimName: String, objects: List<ScoredObject>): Boolean {
        val keyed = objectValue(objects, normalize(f.leaf))
        val id = victimId(objects, normalize(f.leaf))
        val candidates = when {
            keyed != null -> listOf(keyed)
            f.kind == "num" -> listOfNotNull(id)
            hasIdToken(f.leaf) -> listOfNotNull(id, victimName)
            else -> listOf(victimName) + listOfNotNull(id)
        }
        for (c in candidates) {
            if (setField(f, c)) {
                return true
            }
        }
        return false
    }

    private fun setRoleFieldToReduced(action: RestCallAction, reducedRole: String): List<String>? {
        val f = roleField(action) ?: return null
        val ok = if (reducedRole == emptyRoleList) clearArray(f) else setField(f, reducedRole)
        return if (ok) listOf(f.key) else null
    }

    private fun keepOnlyTargetFields(action: RestCallAction, keep: Set<String>) {
        val removed = mutableListOf<String>()
        for (f in schemaFields(action)) {
            if (f.key in keep) continue
            val gene = f.gene
            if (f.loc == "body" && gene is OptionalGene && gene.isActive && "." !in f.name) {
                gene.isActive = false
                removed.add(f.name)
            }
            if (f.loc == "query" && gene is OptionalGene && gene.isActive) {
                gene.isActive = false
                removed.add(f.name)
            }
        }
        log.debug("Stateful-authorization: removed optional fields $removed from ${action.getName()}")
    }

    private fun setUserNameFieldsToVictim(
        action: RestCallAction,
        victimAuth: HttpWsAuthenticationInfo,
        targeted: List<String>
    ) {
        val idKeys = identityKeys(victimAuth, "")
        if (idKeys.isEmpty()) return
        val set = mutableListOf<String>()
        for (f in schemaFields(action)) {
            if (f.loc != "body" || f.kind != "str" || f.key in targeted || normalize(f.leaf) !in idKeys) {
                continue
            }
            if (setField(f, victimAuth.name)) {
                set.add(f.name)
            }
        }
        if (set.isNotEmpty()) {
            log.debug("Stateful-authorization: set user-name fields $set to '${victimAuth.name}' on ${action.getName()}")
        }
    }

    private fun routeLooksMissing(candidate: RestCallAction): Boolean {
        val path = candidate.path.toString()
        if (!path.substringAfterLast("/").startsWith("{")) {
            return false
        }
        val parent = path.substringBeforeLast("/")
        if (parent.contains("{")) {
            return false
        }
        var calledParent = false
        var all404 = true
        for (ea in RestIndividualSelectorUtils.findEvaluatedActions(individualsInSolution, authenticated = true)) {
            val action = ea.action
            if (action !is RestCallAction) {
                continue
            }
            val p = action.path.toString()
            if (p != path && p != parent) {
                continue
            }
            if (p == parent) {
                calledParent = true
            }
            val result = ea.result
            val code = if (result is RestCallResult) result.getStatusCode() else null
            if (code != 404) {
                all404 = false
            }
        }
        return calledParent && all404
    }

    private fun trySetFromStringValue(g: Gene, value: String): Boolean =
        try {
            g.setFromStringValue(value)
        } catch (e: Exception) {
            false
        }

    private fun addForInjections() {

        if (!config.isEnabledFaultCategory(DefinedFaultCategory.XSS)) {
            log.debug("Skipping security test for XSS as disabled in configuration")
        } else {
            if(hasPhaseTimedOut()) return
            handleXSSCheck()
        }

        if (!config.isEnabledFaultCategory(DefinedFaultCategory.SQL_INJECTION)) {
            log.debug("Skipping experimental security test for sql injection as disabled in configuration")
        } else {
            if(config.blackBox || sampler.isSUTUsingASQLDatabase()) {
                // in white-box testing, if no that the SUT is not using any SQL database, then no point
                // in trying any kind of SQLi attack
                if(hasPhaseTimedOut()) return
                handleSqlICheck()
            }
        }

        if (config.isEnabledFaultCategory(DefinedFaultCategory.SSRF)) {
            if(hasPhaseTimedOut()) return
            ssrfAnalyser.apply()
        }
    }

    private fun addForInfoLeakage() {

        if(!config.isEnabledFaultCategory(DefinedFaultCategory.SECURITY_EXISTENCE_LEAKAGE)){
            log.debug("Skipping security test for existence leakage as disabled in configuration")
        } else {
            // getting 404 instead of 403
            if(hasPhaseTimedOut()) return
            handleExistenceLeakage()
        }

        if (!config.isEnabledFaultCategory(DefinedFaultCategory.SECURITY_LEAKED_STACK_TRACES)) {
            log.debug("Skipping experimental security test for stack traces as disabled in configuration")
        } else {
            if(hasPhaseTimedOut()) return
            handleStackTraceCheck()
        }

        if(config.isEnabledFaultCategory(DefinedFaultCategory.SECURITY_HIDDEN_ACCESSIBLE_ENDPOINT)){
            if(hasPhaseTimedOut()) return
            handleHiddenAccessibleEndpoint()
        }
    }



    private fun accessControlBasedOnRESTGuidelines() {

        if(!config.isEnabledFaultCategory(DefinedFaultCategory.SECURITY_WRONG_AUTHORIZATION)){
            log.debug("Skipping security test for forbidden but ok others as disabled in configuration")
        } else {
            // quite a few rules here that can be defined
            if(hasPhaseTimedOut()) return
            handleForbiddenOperationButOKOthers(HttpVerb.DELETE)
            if(hasPhaseTimedOut()) return
            handleForbiddenOperationButOKOthers(HttpVerb.PUT)
            if(hasPhaseTimedOut()) return
            handleForbiddenOperationButOKOthers(HttpVerb.PATCH)
        }

        if(!config.isEnabledFaultCategory(DefinedFaultCategory.SECURITY_NOT_RECOGNIZED_AUTHENTICATED)){
            log.debug("Skipping security test for not recognized authenticated as disabled in configuration")
        } else {
            //authenticated, but wrongly getting 401 (eg instead of 403)
            if(hasPhaseTimedOut()) return
            handleNotRecognizedAuthenticated()
        }

        if(!config.isEnabledFaultCategory(DefinedFaultCategory.SECURITY_IGNORE_ANONYMOUS)) {
            log.debug("Skipping experimental security test for forgotten authentication as disabled in configuration")
        } else {
            if(hasPhaseTimedOut()) return
            handleForgottenAuthentication()
        }

        if (!config.isEnabledFaultCategory(DefinedFaultCategory.SECURITY_ANONYMOUS_MODIFICATIONS)) {
            log.debug("Skipping experimental security test for anonymous write as disabled in configuration")
        } else {
            if(hasPhaseTimedOut()) return
            handleAnonymousWriteCheck()
        }

    }


    private fun handleSqlICheck(){

        val K = config.sqliBaselineMaxResponseTimeMs

        mainloop@ for(action in actionDefinitions){

            if(hasPhaseTimedOut()) return

            // Find individuals with 2xx response for this endpoint
            val successfulIndividuals = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                action.verb,
                action.path,
                statusGroup = StatusGroup.G_2xx
            )

            if(successfulIndividuals.isEmpty()){
                continue
            }

            val candidates = successfulIndividuals.mapNotNull { ei ->
                val actionIndex = RestIndividualSelectorUtils.findIndexOfAction(
                    ei,
                    action.verb,
                    action.path,
                    statusGroup = StatusGroup.G_2xx
                )

                if(actionIndex < 0){
                    null
                } else {
                    val action = ei.individual.seeMainExecutableActions()[actionIndex]
                    val result = ei.seeResult(action.getLocalId()) as HttpWsCallResult
                    val time = result.getResponseTimeMs()
                    if(time == null || time >= K ){
                        //make sure the call didn't take too long
                        null
                    } else {
                        // Slice to keep only up to the target action
                        RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(ei.individual, actionIndex)
                    }
                }
            }

            //due to timing, the candidates might be empty
            if(candidates.isEmpty()){
                continue
            }

            // Take the smallest successful individual
            val target = candidates.minBy { it.size() }

            // Try each sqli payload (but only add one test per endpoint)
            for(payload in SQLI_PAYLOADS){

                // Create a copy of the individual
                val copy = target.copy() as RestIndividual
                val actionCopy = copy.seeMainExecutableActions().last()

                val genes = GeneUtils.getAllStringFields(actionCopy.parameters)
                    .filter { it.staticCheckIfImpactPhenotype() }

                if(genes.isEmpty()){
                    continue@mainloop
                }
                var anySuccess = false

                //here we try to modify ALL potential genes
                genes.forEach {
                        gene ->
                    val leafGene = gene.getLeafGene().getPhenotype()
                    if(leafGene !is StringGene){
                        return@forEach
                    }
                    //TODO check if gene is linked with previous actions that create resources with IDs

                    // we need to do this way because we need to append our payload
                    val newPayload = leafGene.getValueAsRawString() +
                            String.format(payload, config.sqliInjectedSleepDurationMs/1000.0)

                    // append the SQLi payload value
                    leafGene.setFromStringValue(newPayload).also {
                        if(it) anySuccess = true
                    }
                }

                if(!anySuccess){
                    continue
                }

                val newInd = builder.merge(target, copy)

                newInd.modifySampleType(SampleType.SECURITY)
                newInd.ensureFlattenedStructure()

                val evaluatedIndividual = fitness.computeWholeAchievedCoverageForPostProcessing(newInd)

                if (evaluatedIndividual == null) {
                    log.warn("Failed to evaluate constructed individual in handleSqlICheck")
                    continue@mainloop
                }

                val faultsCategories = DetectedFaultUtils.getDetectedFaultCategories(evaluatedIndividual)

                if(DefinedFaultCategory.SQL_INJECTION in faultsCategories){
                    val added = archive.addIfNeeded(evaluatedIndividual)
                    assert(added)
                    continue@mainloop
                }
            }
        }
    }

    /**
     *   If we send request on endpoint path with wrong verb, we get 405/501.
     *   When sending OPTIONS, the response should have `Allow` telling what is there.
     *   That info might be different from what specified in the schema.
     *   Should check if mismatches with OpenAPI schemas, eg if an extra verbs.
     *   Let's make a call to those, with valid path, but no query parameters nor any body payloads.
     *   If we get anything but 405/501 then we discovered a hidden accessible endpoint
     */
    private fun handleHiddenAccessibleEndpoint() {

        val actions = actionDefinitions.distinctBy { it.path }

        mainloop@for (a in actions){

            if(hasPhaseTimedOut()) return

            /*
                first build an action to make a OPTION call on each different path
             */
            val pathVariables = a.parameters
                .filterIsInstance<PathParam>()
                .map { it.copy() }
                .toMutableList()

            val verb = HttpVerb.OPTIONS
            val path = a.path.copy()
            val actionId = "$verb$path"
            val authOptions = authSettings.getOfType(HttpWsAuthenticationInfo::class.java)
            val auth = if(authOptions.isNotEmpty()){
                authOptions.first()
            } else {
                HttpWsNoAuth()
            }

            val options = RestCallAction(actionId,verb, path, pathVariables, auth)
            options.doInitialize(randomness)

            //create individual to make the OPTIONS call
            val ind = RestIndividual(mutableListOf(options), SampleType.SECURITY)
            ind.doGlobalInitialize(searchGlobalState)
            ind.ensureFlattenedStructure()

            val evaluatedIndividual = fitness.computeWholeAchievedCoverageForPostProcessing(ind)

            if (evaluatedIndividual == null) {
                log.warn("Failed to evaluate OPTION call")
                continue@mainloop
            }
            archive.addIfNeeded(evaluatedIndividual)

            //now time to check the HTTP response from the OPTIONS call
            val em = evaluatedIndividual.evaluatedMainActions()
            if(em.isEmpty()){
                log.warn("Failed in evaluation of OPTION call")
                continue@mainloop
            }

            val response = em.first().result as RestCallResult
            val fromAllow = response.getAllowedVerbs()
            if(fromAllow == null || fromAllow.isEmpty()){
                continue@mainloop
            }

            //is there any difference from what declared in the schema?
            val hidden = filterHiddenVerbs(path, fromAllow)

            hidden@for(h in hidden){
                //try to make such calls, after the OPTIONS
                val target = RestCallAction("$h:$path",h, path, pathVariables.map { it.copy() }.toMutableList(), auth)
                target.resetLocalIdRecursively()
                //target.doInitialize(randomness) // we are copying params directly

                val x = RestIndividual(mutableListOf(options.copy(), target), SampleType.SECURITY)
                x.doGlobalInitialize(searchGlobalState)
                x.ensureFlattenedStructure()

                val ei = fitness.computeWholeAchievedCoverageForPostProcessing(x)

                if (ei == null) {
                    log.warn("Failed to evaluate OPTIONS+TARGET call")
                    continue@hidden
                }
                //whether it is going to be added depends on the response status of the "target" call
                archive.addIfNeeded(ei)
            }
        }
    }

    fun filterHiddenVerbs(path: RestPath, allowed: Set<HttpVerb>) : Set<HttpVerb>{
        return allowed.filter { it != HttpVerb.OPTIONS
                    && it != HttpVerb.HEAD
                    && !callGraph.isDeclared(it, path)
        }.toSet()
    }

    /**
     * Checks whether any response body contains a stack trace, which would constitute a security issue.
     * Stack traces expose internal implementation details that can aid attackers in exploiting vulnerabilities.
     *
     * Note: This is a best-effort oracle that may produce false positives, as some applications might
     * legitimately return stack traces as part of their business logic.
     *
     * This check is performed only at the end of the search, not during each fitness evaluation,
     * to avoid performance overhead during the main search phase.
     */
    private fun handleStackTraceCheck(){

        mainloop@ for(action in actionDefinitions){

            if(hasPhaseTimedOut()) return

            val suspicious = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                action.verb,
                action.path,
                status = 500,
            )

            if(suspicious.isEmpty()){
                continue
            }

            for(target in suspicious) {
                var isFaultFound = false

                val copyTarget = target.copy()
                //  we need BOTH the check here and in the fitness function.
                //  here: because we need to make sure 500 from archive are re-executed and added back with SECURITY tag if fault found
                //  in ff: to avoid losing info if test is re-evaluated

                isFaultFound = copyTarget.evaluatedMainActions()
                    .asSequence()
                    .filter { (it.action as RestCallAction).verb == action.verb && it.action.path == action.path }
                    .mapNotNull { it.result as? RestCallResult }
                    .any { r ->
                        val body = r.getBody()
                        r.getStatusCode() == 500 &&
                                body != null &&
                                StackTraceUtils.looksLikeStackTrace(body)
                    }

                if(isFaultFound){
                    copyTarget.individual.modifySampleType(SampleType.SECURITY)
                    copyTarget.individual.ensureFlattenedStructure()
                    val evaluatedIndividual = fitness.computeWholeAchievedCoverageForPostProcessing(copyTarget.individual)

                    if (evaluatedIndividual == null) {
                        log.warn("Failed to evaluate constructed individual in handleStackTraceCheck")
                        continue@mainloop
                    }

                    val added = archive.addIfNeeded(evaluatedIndividual)
                    assert(added)
                    continue@mainloop
                }
            }
        }
    }

    /**
     * Anonymous Write Check - Detects missing authentication on write operations.
     *
     * This check flags:
     * - PUT returning 2xx (except 201) without authentication - updating existing resources
     * - PATCH returning 2xx without authentication - partial updates
     * - DELETE returning 2xx without authentication - deleting resources
     *
     * Note: PUT returning 201 (creating new resource) might be acceptable for public endpoints
     * like adding entries to a public forum.
     */
    private fun handleAnonymousWriteCheck(){
        mainloop@ for(action in actionDefinitions){

            if(action.verb != HttpVerb.PUT && action.verb != HttpVerb.PATCH && action.verb != HttpVerb.DELETE){
                continue
            }

            if(hasPhaseTimedOut()) return

            val suspicious = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                action.verb,
                action.path,
                statusGroup = StatusGroup.G_2xx,
                authenticated = false
            )

            if(suspicious.isEmpty()){
                continue
            }

            // Take the smallest suspicious individual
            val target = suspicious.minBy { it.individual.size() }

            val actionIndex = RestIndividualSelectorUtils.findIndexOfAction(
                target,
                action.verb,
                action.path,
                statusGroup = StatusGroup.G_2xx,
                authenticated = false
            )

            if(actionIndex < 0){
                continue
            }

            // Check if this is a vulnerability
            val actionResult = target.evaluatedMainActions()[actionIndex].result as? RestCallResult
            if(actionResult == null){
                continue
            }

            val statusCode = actionResult.getStatusCode()

            // For PUT: only flag if it's NOT 201 (resource creation might be OK, update is not)
            if(action.verb == HttpVerb.PUT && statusCode == 201){
                continue
            }

            // This is a vulnerability: write operation without authentication
            val sliced = RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
                target.individual,
                actionIndex
            )

            sliced.modifySampleType(SampleType.SECURITY)
            sliced.ensureFlattenedStructure()

            val evaluatedIndividual = fitness.computeWholeAchievedCoverageForPostProcessing(sliced)
            if (evaluatedIndividual == null) {
                log.warn("Failed to evaluate constructed individual in handleAnonymousWriteCheck")
                continue@mainloop
            }

            val faultsCategories = DetectedFaultUtils.getDetectedFaultCategories(evaluatedIndividual)

            if(DefinedFaultCategory.SECURITY_ANONYMOUS_MODIFICATIONS in faultsCategories){
                val added = archive.addIfNeeded(evaluatedIndividual)
                assert(added)
                continue@mainloop
            }
        }
    }
    /**
     * Authenticated user A accesses endpoint X, but get 401 (instead of 403).
     * In theory, a bug. But, could be false positive if A is misconfigured.
     * How to check it?
     * See if on any other endpoint Y we get a 2xx with A.
     * But, maybe Y does not need authentication...
     * so, check if there is any test case for which on Y we get a 401 or 403.
     * if yes, then X is buggy, as should had rather returned 403 for A.
     */
    private fun handleNotRecognizedAuthenticated() {

        mainloop@ for(action in actionDefinitions){

            if(hasPhaseTimedOut()) return

            val suspicious = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                action.verb,
                action.path,
                status = 401,
                authenticated = true
            ).map { RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
                it,
                action.verb,
                action.path,
                status = 401,
                authenticated = true
            )
            }.distinctBy { it.seeMainExecutableActions().last().auth.name }

            if(suspicious.isEmpty()){
                continue
            }

            for(target in suspicious) {

                val user = target.seeMainExecutableActions().last().auth.name

                val ok = RestIndividualSelectorUtils.findIndividuals(
                    individualsInSolution,
                    statusGroup = StatusGroup.G_2xx,
                    authenticatedWith = user
                ).map { RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
                    it,
                    statusGroup = StatusGroup.G_2xx,
                    authenticatedWith = user)
                }.distinctBy { it.seeMainExecutableActions().last().getName() }

                if(ok.isEmpty()){
                    continue
                }

                /*
                    so, the given suspicious user that got 401 can get a 2xx on an endpoint.
                    has anyone got a 401 or 403 on this endpoint?
                    actually, could even be same user, eg when trying to access resource of
                    another user could get a 403
                */
                for(success in ok){
                    val last = success.seeMainExecutableActions().last()
                    val with401or403 = RestIndividualSelectorUtils.findIndividuals(
                        individualsInSolution,
                        verb = last.verb,
                        path = last.path,
                        statusCodes = listOf(401,403),
                        authenticated = true
                    ).map {
                        RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
                            it,
                            verb = last.verb,
                            path = last.path,
                            statusCodes = listOf(401,403),
                            authenticated = true
                        )
                    }
                    if(with401or403.isEmpty()){
                        continue
                    }
                    // if reach here, we got a bug
                    val auth = with401or403.minBy { it.size() }

                    val final = builder.merge(auth,success,target)
                    final.modifySampleType(SampleType.SECURITY)
                    final.ensureFlattenedStructure()

                    val evaluatedIndividual = fitness.computeWholeAchievedCoverageForPostProcessing(final)
                    if (evaluatedIndividual == null) {
                        log.warn("Failed to evaluate constructed individual in handleNotRecognizedAuthenticated")
                        continue
                    }

                    val added = archive.addIfNeeded(evaluatedIndividual)
                    assert(added)
                    continue@mainloop
                }
            }
        }
    }


    /**
     * Accessing a protected GET endpoint with id with not authorized should return 403, even if not exists.
     * otherwise, if returning 404, we can find out that the resource does not exist.
     */
    private fun handleExistenceLeakage(){

        val getOperations = RestIndividualSelectorUtils.getAllActionDefinitions(actionDefinitions, HttpVerb.GET)

        getOperations.forEach { get ->

            if(hasPhaseTimedOut()) return

            val inds403 = RestIndividualSelectorUtils.findAndSlice(
                individualsInSolution,
                HttpVerb.GET,
                get.path,
                status = 403
            )
            if(inds403.isEmpty()){
                return@forEach
            }

            val inds404 = RestIndividualSelectorUtils.findAndSlice(
                individualsInSolution,
                HttpVerb.GET,
                get.path,
                status = 404
            )
            if(inds404.isEmpty()){
                return@forEach
            }

            //found the bug.
            val forbidden = inds403.minBy { it.size() }
            val notfound = inds404.minBy { it.size() }

            val final = builder.merge(forbidden, notfound)

            // Check if the 404 path is a child resource and add parent GET to check access
            val path404 = get.path
            val action404 = final.seeMainExecutableActions().last()
            val lastAuth = action404.auth

            // Find the parent path from getOperations (all GET operation definitions)
            val parentGetOperation = getOperations
                .filter { it.path.isStrictlyAncestorOf(path404)}
                .filter { it.path.isLastElementAParameter() }
                .minByOrNull { it.path.levels() }

            if (parentGetOperation != null) {
                val parentGetAction = parentGetOperation.copy() as RestCallAction
                parentGetAction.resetLocalIdRecursively()
                parentGetAction.forceNewTaints()

                parentGetAction.doInitialize()
                parentGetAction.auth = lastAuth
                // Bind to the same path params from the 404 action to ensure same IDs
                //FIXME this would currently not work for dynamic parameters
                parentGetAction.bindToSamePathResolution(action404)

                final.addResourceCall(
                    restCalls = RestResourceCalls(
                        actions = mutableListOf(parentGetAction),
                        sqlActions = listOf()
                    )
                )
            }

            final.modifySampleType(SampleType.SECURITY)
            final.ensureFlattenedStructure()

            val evaluatedIndividual = fitness.computeWholeAchievedCoverageForPostProcessing(final)
            if (evaluatedIndividual == null) {
                log.warn("Failed to evaluate constructed individual in handleExistenceLeakage")
                return@forEach
            }

            val faultsCategories = DetectedFaultUtils.getDetectedFaultCategories(evaluatedIndividual)

            if(DefinedFaultCategory.SECURITY_EXISTENCE_LEAKAGE in faultsCategories){
                // add the evaluated individual to the archive
                val added = archive.addIfNeeded(evaluatedIndividual)
                //if we arrive here, should always be added, because we are creating a new testing target
                assert(added)
            }

        }
    }


    /**
     * Given a target verb like DELETE,
     * here we are considering this case:
     * - authenticated user A creates a resource X (status 2xx) | or possibly via SQL insertions
     * - authenticated user B gets 403 on DELETE X
     * - authenticated user B gets 200 on PUT/PATCH on X
     */
    private fun handleForbiddenOperationButOKOthers(targetVerb: HttpVerb) {

        /*
    what needs to be done here:
    - check if at least 2 users. if not, nothing to do
    - from schema, check all DELETE operations
    - from archive, search if there is any test with a DELETE returning a 403
    - do that for every different endpoint. There are 2 options:
    -- (1) there is such call,  then
    ---     make a copy of the individual
    ----    do a "slice" and remove all calls after the DELETE call (if any)
    -- (2) there is not. need to create it based on successful create resources with authenticated user
    ---    search for create resource for endpoint of DELETE
    ---    do slice and remove calls after create resource endpoint call
    ---    add a DELETE with different user (verify get a 403)
    ---    make sure that DELETE is bound on some resource path as the create operation
    - append new REST Call action (see mutator classes) for PATCH/PUT with different auth, based
      on action copies from action definitions. should be on same endpoint.
    - need to resolve path element parameters to point to same resolved endpoint as DELETE
    - as PUT/PATCH requires payloads and possible valid query parameters, search from archive an
      existing action that returns 2xx, and copy it to use as starting point
    - execute new test case with fitness function
    - create new testing targets based on status code of new actions
    - add to archive (if needed)
 */

        // Check if at least 2 users. if not, nothing to do
        if (!checkForAtLeastNumberOfAuthenticatedUsers(2)) {
            return
        }

        // From schema, check all operations for target verb X, in order to do that
        // obtain all X operations in the SUT according to the Swagger
        val verbOperations = RestIndividualSelectorUtils.getAllActionDefinitions(actionDefinitions, targetVerb)

        verbOperations.forEach { call ->

            val individualWith403LastCall = findOrCreateTestFor403(call.path, targetVerb)
                ?: return@forEach

            // After having a set of requests in which the last one is a 403 DELETE (for example) call with another user,
            // add a PUT or PATCH (for example) with same user as 403 DELETE
            addWronglySuccessOperation(individualWith403LastCall, targetVerb)
        }
    }



    private fun addWronglySuccessOperation(
        individualWith403LastCall: RestIndividual,
        verb: HttpVerb
    ) {
        //at this point, the individual we are building should end with a 403 call.
        //however, recall that, as the fitness function is not executed yet,
        //we cannot be sure of returned status code
        val lastAction = individualWith403LastCall.seeMainExecutableActions().last()
        assert(lastAction.verb == verb)

        val actions = HttpVerb.otherWriteOperationsOnSameResourcePath(verb)
            .mapNotNull {
                RestIndividualSelectorUtils.findAction(
                    individualsInSolution,
                    it,
                    lastAction.path,
                    statusGroup = StatusGroup.G_2xx
                )?.copy() as RestCallAction?
            }


        actions.forEach {
            it.resetLocalIdRecursively()
            it.forceNewTaints()
            //make sure using same auth
            it.auth = lastAction.auth
            it.usePreviousLocationId = lastAction.usePreviousLocationId
            it.bindBasedOn(lastAction.path, lastAction.parameters.filterIsInstance<PathParam>(), null)

            //create new individual where this action on same path and auth that led to 403 is added
            val finalIndividual = individualWith403LastCall.copy() as RestIndividual
            finalIndividual.addResourceCall(
                restCalls = RestResourceCalls(
                    actions = mutableListOf(it),
                    sqlActions = listOf()
                )
            )

            finalIndividual.seeMainExecutableActions().filter { it.verb == HttpVerb.PUT || it.verb == HttpVerb.POST }.forEach{
                it.saveCreatedResourceLocation = true
            }
            finalIndividual.fixResourceForwardLinks()

            finalIndividual.modifySampleType(SampleType.SECURITY)
            finalIndividual.ensureFlattenedStructure()

            val evaluatedIndividual = fitness.computeWholeAchievedCoverageForPostProcessing(finalIndividual)
            if (evaluatedIndividual == null) {
                log.warn("Failed to evaluate constructed individual in security testing phase")
                return@forEach
            }
            //at this point, we have a new evaluated individual.
            //if there was any security issue, that should had been detected in fitness function!!!
            //not here.
            //this is because otherwise phases like minimization would be broken.

            //anyway, let's verify indeed second last action if a 403 target verb. otherwise, it is a problem
            val ema = evaluatedIndividual.evaluatedMainActions()

            val n = evaluatedIndividual.individual.seeMainExecutableActions().size
            if(ema.size != n){
                log.warn("Failed to build security test. Premature stopping of HTTP call sequence")
                return@forEach
            }

            val secondLast = ema[ema.size - 2]
            val secondLastAction = secondLast.action
            val secondLastResult = secondLast.result
            if(secondLastAction !is RestCallAction || secondLastResult !is RestCallResult) {
                //shouldn't really ever happen...
                //TODO should refactor code to enforce generics in subclasses
                log.warn("Wrong type: non-REST action/result")
                return@forEach
            }
            if (secondLastAction.verb != verb ||  secondLastResult.getStatusCode() != 403) {
                log.warn("Issue with constructing evaluated individual. Expected a 403 $verb," +
                        " but got: ${secondLastResult.getStatusCode()} ${secondLastAction.verb}")
                return@forEach
            }

            /*
                FIXME: isn't this wrong??? ie, should be done in fitness function
             */
            val scenarioId = idMapper.handleLocalTarget("security:forbidden$verb:${lastAction.path}")
            evaluatedIndividual.fitness.updateTarget(scenarioId, 1.0)

            // add the evaluated individual to the archive
            val added = archive.addIfNeeded(evaluatedIndividual)
            //if we arrive here, should always be added, because we are creating a new testing target
            assert(added)
        }
    }


    /**
     * Check if there is a test case with a 403 and another one with a 200 without authentication.
     * To check this, there must be a resource. It can either be newly created or already exist,
     * such as during initialization. While the user who created this
     * resource can access it (200), the other user cannot (403). However, if a 200 status code is
     * returned when attempting to access the same resource without sending the authorization header,
     * it indicates that authorization checks are wrongly ignored if no auth info is set.
     * Example:
     * POST /resources/ AUTH1 -> 201 (location header: /resources/42/)
     * GET /resources/42/ AUTH1 -> 200
     * GET /resources/42/ AUTH2 -> 403
     * GET /resources/42/ NOAUTH -> 200
     */
    private fun handleForgottenAuthentication() {
        actionDefinitions.forEach { op ->

            if(hasPhaseTimedOut()) return

            val ind403or401 = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                op.verb,
                op.path,
                statusCodes = listOf(401,403)
            )

            if (ind403or401.isEmpty()) {
                return@forEach //there is not any protected resource for this path/verb.
            }

            val i2xx = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                op.verb,
                op.path,
                statusGroup = StatusGroup.G_2xx,
                authenticated = false
            )

            if(i2xx.isNotEmpty()){
                // we have a 2xx without auth, so we can create a test case
                // we can just take the smallest 403 or 401 and the smallest 2xx

                // FIXME: mocked external services might return 401/403 or 2xx without auth.
                // in this case, we couldn't merge them because of "child already present" error.
                // we need to fix this.

                val first = ind403or401.minBy { it.individual.size() }

                val actionIndexFirst = RestIndividualSelectorUtils.findIndexOfAction(
                    first,
                    op.verb,
                    op.path,
                    statusCodes = listOf(401,403)
                )

                val firstSliced = RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
                    first.individual,
                    actionIndexFirst
                )


                val second = i2xx.minBy { it.individual.size() }.copy()
                val actionIndexSecond = RestIndividualSelectorUtils.findIndexOfAction(
                    second,
                    op.verb,
                    op.path,
                    statusGroup = StatusGroup.G_2xx,
                    authenticated = false
                )
                val secondSliced = RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
                    second.individual,
                    actionIndexSecond
                )

                secondSliced.removeHostnameResolutionAction(firstSliced.seeAllActions().filter {
                    it is HostnameResolutionAction
                } as List<HostnameResolutionAction>)

                val finalIndividual = builder.merge(
                    firstSliced,
                    secondSliced
                )

                finalIndividual.modifySampleType(SampleType.SECURITY)
                finalIndividual.ensureFlattenedStructure()
                org.evomaster.core.Lazy.assert { finalIndividual.verifyValidity(); true }
                val ei = fitness.computeWholeAchievedCoverageForPostProcessing(finalIndividual)
                if (ei != null) {
                    val added = archive.addIfNeeded(ei)
                    assert(added)
                }

                return@forEach
            }

            // if we arrive here, we have a 403 or 401, but no 2xx without auth. Now, we can try to create one
            val candidates = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                op.verb,
                op.path,
                statusGroup = StatusGroup.G_2xx,
                authenticated = true
            )
            if (candidates.isEmpty()) {
                return@forEach
            }

            candidates.forEach { ind ->

                // we have a candidate individual with a 2xx on the same path/verb
                // we need to copy the last action, which is the one that returns 2xx
                val action2xx = RestIndividualSelectorUtils.findIndexOfAction(
                    ind,
                    op.verb,
                    op.path,
                    statusGroup = StatusGroup.G_2xx,
                )

                val slicedIndividual = RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
                    ind.individual,
                    action2xx
                )

                val copyLast = slicedIndividual.seeMainExecutableActions().last().copy() as RestCallAction
                val copyNoAuthLast = copyLast.copy() as RestCallAction

                copyLast.resetLocalIdRecursively()
                copyLast.forceNewTaints()
                copyNoAuthLast.resetLocalIdRecursively()
                copyNoAuthLast.forceNewTaints()


                val otherUsers = authSettings.getAllOthers(copyLast.auth.name, HttpWsAuthenticationInfo::class.java)

                otherUsers.forEach { other ->
                    val finalIndividual = slicedIndividual.copy() as RestIndividual

                    // we need to set the auth for the last action to the other user
                    copyLast.auth = other
                    // and for the no auth one, we set it to NoAuth
                    copyNoAuthLast.auth = HttpWsNoAuth()

                    finalIndividual.addResourceCall(
                        restCalls = RestResourceCalls(
                            actions = mutableListOf(copyLast, copyNoAuthLast),
                            sqlActions = listOf()
                        )
                    )
                    finalIndividual.seeMainExecutableActions()
                        .filter { it.verb == HttpVerb.PUT || it.verb == HttpVerb.POST }.forEach {
                            it.saveCreatedResourceLocation = true
                        }
                    finalIndividual.fixResourceForwardLinks()

                    finalIndividual.modifySampleType(SampleType.SECURITY)
                    finalIndividual.ensureFlattenedStructure()
                    org.evomaster.core.Lazy.assert { finalIndividual.verifyValidity(); true }

                    val ei = fitness.computeWholeAchievedCoverageForPostProcessing(finalIndividual)
                    if (ei != null) {
                        archive.addIfNeeded(ei)
                    }
                }
            }
        }
    }

    /**
     * XSS (Cross-Site Scripting) check.
     *
     * Creates test cases for both reflected and stored XSS by injecting malicious payloads
     * into string parameters. For each endpoint with a 2xx response:
     * - Injects XSS payload into string fields (body, query, path parameters)
     * - For POST/PUT/PATCH: attempts to add a GET on the same path for stored XSS detection
     *
     */

    private fun handleXSSCheck(){

        mainloop@ for(action in actionDefinitions){

            if(hasPhaseTimedOut()) return

            // Find individuals with 2xx response for this endpoint
            val successfulIndividuals = RestIndividualSelectorUtils.findAndSlice(
                individualsInSolution,
                action.verb,
                action.path,
                statusGroup = StatusGroup.G_2xx
            )

            if(successfulIndividuals.isEmpty()){
                continue
            }

            // Take the smallest successful individual
            val target = successfulIndividuals.minBy { it.size() }


            // Try each XSS payload (but only add one test per endpoint)
            for(payload in XSS_PAYLOADS){

                // Create a copy of the individual
                var copy = target.copy() as RestIndividual
                val actionCopy = copy.seeMainExecutableActions().last()

                val genes = GeneUtils.getAllStringFields(actionCopy.parameters)
                    .filter { it.staticCheckIfImpactPhenotype() }

                if(genes.isEmpty()){
                    continue@mainloop
                }

                val anySuccess = genes.map { gene ->
                    gene.setFromStringValue(payload)
                }.any { it }

                if(!anySuccess){
                    continue
                }

                // Try to add a linked GET operation for stored XSS detection
                //TODO to properly handle POST, we need first to finish the work on CallGraphService
                //FIXME ie we need to guarantee it is working on same resource
                if(action.verb == HttpVerb.POST || action.verb == HttpVerb.PUT || action.verb == HttpVerb.PATCH){
                    copy = tryAttachLinkedGetForStoredXSS(
                        ind = copy,
                        path = actionCopy.path,
                        payload = payload
                    ) ?: copy
                }

                copy.modifySampleType(SampleType.SECURITY)
                copy.ensureFlattenedStructure()

                try {
                    val evaluatedIndividual = fitness.computeWholeAchievedCoverageForPostProcessing(copy)

                    if (evaluatedIndividual == null) {
                        log.warn("Failed to evaluate constructed individual in handleXSSCheck")
                        continue@mainloop
                    }

                    val faultsCategories = DetectedFaultUtils.getDetectedFaultCategories(evaluatedIndividual)

                    if(DefinedFaultCategory.XSS in faultsCategories){
                        archive.addIfNeeded(evaluatedIndividual)
                        continue@mainloop
                    }
                } catch(e: Exception){
                    // For certain malformed or encoded requests (such as /api/cleanup/items/<img src=x onerror=alert('XSS')>
                    // which becomes /api/cleanup/items/%3Cimg%20src=x%20onerror=alert('XSS')%3E), the framework may throw
                    // a "URI is not absolute" error due to invalid or non-absolute path handling. Such cases can occur when
                    // XSS-like payloads are injected or when user input is not properly sanitized. The try-catch block ensures
                    // that these exceptions do not interrupt the main processing loop.

                    log.warn("Failed to evaluate constructed individual in handleXSSCheck: ${e.message}")
                }
            }
        }
    }

    private fun tryAttachLinkedGetForStoredXSS(
        ind: RestIndividual,
        path: RestPath,
        payload: String
    ): RestIndividual? {
        //TODO to properly handle POST, we need first to finish the work on CallGraphService
        val getIndividuals = RestIndividualSelectorUtils.findIndividuals(
            individualsInSolution,
            HttpVerb.GET,
            path,
            statusGroup = StatusGroup.G_2xx
        )
        if (getIndividuals.isEmpty()) return null

        val getInd = getIndividuals.first()
        val getActionIndex = RestIndividualSelectorUtils.findIndexOfAction(
            getInd,
            HttpVerb.GET,
            path,
            statusGroup = StatusGroup.G_2xx
        )
        if (getActionIndex < 0) return null

        val second = RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
            getInd.individual,
            getActionIndex
        )

        val getAction = second.seeMainExecutableActions().last() as RestCallAction

        val genes = GeneUtils.getAllStringFields(getAction.parameters)
            .filter { it.staticCheckIfImpactPhenotype() }
        if (genes.isEmpty()) return null

        val anySuccess = genes.map { gene ->
            gene.setFromStringValue(payload)
        }.any { it }

        if (!anySuccess) return null

        return builder.merge(ind, second)

    }

    /**
     * @return a test where last action is for given path and verb returning 403.
     * null if failed.
     */
    private fun findOrCreateTestFor403(
        path: RestPath,
        verb: HttpVerb,
    ): RestIndividual? {
        // from archive, search if there is any test with given verb returning a 403
        val existing403 = RestIndividualSelectorUtils.findIndividuals(
            individualsInSolution,
            verb,
            path,
            403,
            authenticated = true
        )

        // if there is such an individual
        if (existing403.isNotEmpty()) {

            // current individual in the list of existing 403. Since the list is not empty,
            // we can just get the first item
            val currentIndividualWith403 = existing403[0]

            val actionIndex = RestIndividualSelectorUtils.getIndexOfAction(
                currentIndividualWith403,
                verb,
                path,
                403
            )

            // slice the individual in a way that delete all calls after the chosen verb request
            return RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
                currentIndividualWith403.individual,
                actionIndex
            )
        }

        // there is not. need to create it based on successful create resources with authenticated user
        // but, first let's check if we can have any successfully delete action

        /*
            We have a "verb" (eg, a DELETE) path in form for example
            /users/{id}
            and want to get a _resolved_ creation action (either PUT or POST) for it.
            The new "verb" we are going to create must point to the same resolved action.
            But "verb" could have query parameters and possibly body payloads... all with
            constraints that must be satisfied.
            So we cannot easily just create it from scratch.
            Need to re-use an existing one, if any.
        */
        var successIndividuals = RestIndividualSelectorUtils.findIndividuals(
            individualsInSolution,
            verb,
            path,
            statusGroup = StatusGroup.G_2xx,
        )

        if (successIndividuals.isEmpty()) {
            /*
                This needs a bit of explanation.
                We want to get an action that works, without failed constraint validation on
                query parameters or body payloads.
                Ideally, a 2xx would do.
                But what if we could not create any because they all fail to point to an existing
                resource? if 404, could still be fine, as then we link it to creation operation
             */
            successIndividuals = RestIndividualSelectorUtils.findIndividuals(
                individualsInSolution,
                verb,
                path,
                status = 404
            )
        }
        if (successIndividuals.isEmpty()) {
            //no point trying to create a successful action directly, if none was evolved at all...
            //as likely would fail as well here
            return null
        }

        //start from base test in which resource is created
        val (creationIndividual, creationEndpoint) = RestIndividualSelectorUtils
            .findIndividualWithEndpointCreationForResource(
                individualsInSolution,
                path,
                true
            ) ?: return null

        // find the index of the creation action
        val actionIndexForCreation = creationIndividual.individual.getActionIndex(
            creationEndpoint.verb,
            creationEndpoint.path
        )
        val creationAction = creationIndividual.individual.seeMainExecutableActions()[actionIndexForCreation]
        assert(creationAction.auth !is NoAuth)

        //we don't need anything after the creation action
        val sliced = RestIndividualBuilder.sliceAllCallsInIndividualAfterAction(
            creationIndividual.individual,
            actionIndexForCreation
        )

        // from a success target operation individual,
        // create a new target action on same path,
        // but then change auth
        val targetInd = successIndividuals.first().individual
        val targetActionIndex = targetInd.getActionIndex(verb, path)
        val targetAction = targetInd.seeMainExecutableActions()[targetActionIndex].copy() as RestCallAction
        assert(targetAction.verb == verb && targetAction.path.isEquivalent(path))
        targetAction.resetLocalIdRecursively()
        targetAction.forceNewTaints()
        targetAction.auth =
            authSettings.getDifferentOne(creationAction.auth.name, HttpWsAuthenticationInfo::class.java, randomness)

        //    Bind the creation operation and new target action based on their path
        linkAndBindActions(creationAction, targetAction)

        //finally, add the target action to the test including the creation of the resource
        sliced.addResourceCall(
            restCalls = RestResourceCalls(
                actions = mutableListOf(targetAction),
                sqlActions = listOf()
            )
        )

        return sliced
    }

    private fun linkAndBindActions(
        creationAction: RestCallAction,
        targetAction: RestCallAction
    ) {
        CreateResourceUtils.linkDynamicCreateResource(creationAction, targetAction)
        if (creationAction.path.isEquivalent(targetAction.path)) {
            targetAction.bindBasedOn(creationAction.path, creationAction.parameters.filterIsInstance<PathParam>(), null)
        }
    }


    /**
     * Wrong Authorization
     *
     * User A, access endpoint X, but get 401 (instead of 403).
     * In theory, a bug. But, could be false positive if A is misconfigured.
     * How to check it?
     * See if on any other endpoint Y we get a 2xx with A.
     * But, maybe Y does not need authentication...
     * so, check if there is any test case for which on Y we get a 401 or 403.
     * if yes, then X is buggy, as it should rather have returned 403 for A.
     * This seems to actually happen for familie-ba-sak, new NAV SUT.
     */
    fun handleUnauthorizedInsteadOfForbidden() {

    }

    private fun checkForAtLeastNumberOfAuthenticatedUsers(numberOfUsers: Int): Boolean {

        if (authSettings.size(HttpWsAuthenticationInfo::class.java) < numberOfUsers) {
            LoggingUtil.getInfoLogger()
                .debug("Security test for this method requires at least $numberOfUsers authenticated users")
            return false
        }

        return true
    }

}
