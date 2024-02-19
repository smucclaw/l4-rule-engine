(ns l4-rule-engine.main
  (:require [meander.epsilon :as m]
            [meander.strategy.epsilon :as r]
            [clara.rules :refer [defsession insert fire-rules]]
            [clara.tools.fact-graph :refer [session->fact-graph]]
            [clara.tools.inspect :refer [inspect explain-activations]]
            [l4-rule-engine.clara :refer [->Edge]]))

(def ^:private asked (atom {}))

(defn- asked? [fact]
  (contains? @asked fact))

(defn- add-asked! [fact bool]
  (swap! asked assoc fact bool))

(defn step
  "Axiomatisation of (non-deterministic) small step reduction for an abstract
   machine interpreter for L4.

   Configurations C are tuples of the form〈?ruleset, ?env, ?goals, ?trace〉, where:
   - ?ruleset is a set of rules
   - ?env is the variable environment
   - ?goals is the remaining list of goals to be proven
   - ?trace is the current evaluation trace

   Note here that:
   - ?ruleset is treated as an environment for global defintions, where:
     - Rules of the form (DECIDE ?term IF ?body) are interpreted as global
       definitions of the form:
         def ?term := ?body
   - ?goals which represents the list of goals, is interpreted as a sequence of
     statements
   - When we need to prove a ?term coming from a user-defined rule, we substitute
     it for its ?body in ?ruleset (interpreted as a global environment), and then
     continue evaluating the remaining goals (interpreted as a sequence of statements).

   Key judgement forms:
   - Abstact machine small-step reduction: C ⟶ C'
   - Well-formedness of an environment: ⊢ ?env ok
     - Intuitively, this is used to enforce the simplifying assumption that we
       perform call-by-value reduction and that we only store bindings in
       full head normal form (modulo neutral terms).
       - Note that this means that we are assuming that there are no recursive
         bindings.
   - Big step evaluation for the expression language, with respect to an environment:
          ?env ⊢ ?term ⇓ ?term'

  - Meta-properties:
    - Provability of a goal is equivalent to a reachability property of the form
       〈?ruleset, ?env, [?goal], ?trace〉⊨ EF (?goals = [])
    - Non-provability can come in 2 forms:
      1. Non-termination, ie looping.
      2. Deadlock, because goal in the head of ?goals is not a known fact.

   TODO: Explore normalisation-by-evaluation to prevent exponential blow-up of
   term size caused by naive substitution wrt an environment.

   More reading:
   - https://www.cs.tsukuba.ac.jp/internal/techreport/data/ISE-TR-91-94.pdf
   - https://pages.di.unipi.it/boerger/Papers/LogicPgg/wamFeb94.pdf
   - https://arxiv.org/pdf/2109.01483.pdf
   - https://era.ed.ac.uk/bitstream/handle/1842/13484/Andrews1991.Pdf?isAllowed=y&sequence=1
   - https://www.cs.cmu.edu/~crary/papers/2018/twam.pdf
   - https://homepage.divms.uiowa.edu/~slonnegr/plf/Book/Chapter8.pdf
   "
   [state]
  (if-let [state
           (not-empty
            (m/rewrites state
   ;; For rule applications, we lookup the ?goal in the global rule environment
   ;; and then substitute the current goal statement with its body.
   ;; TODO:
   ;; - Handle the case where the head of the rule, ie ?goal, contains
   ;;   variables that need to be bound in the body.
   ;;   Here, we need to extend the local environment with bindings.
   ;;   Lexical scoping? Can assume or desugar so that we can assume Barendregt
   ;;   convention?
   ;; - Formalise and implement a mechanism to properly select the "next"
   ;;   applicable rule using a global rule env represented as a sequence
   ;;   instead of a set.
   ;;
   ;;  ⊢ ?env ok            (DECIDE ?goal IF ?body) ∈ ?ruleset
   ;; ---------------------------------------------------------- [Rule application]
   ;;〈?ruleset, ?env, ?goal : ?goals, ?trace〉
   ;; ⟶ 〈?ruleset, ?env, ?body : ?goals, (EDGE ?goal ?body) : ?trace〉
   ;;
   ;; This implementation is not so efficient as it performs a linear traversal
   ;; over all clauses to select an applicable one.
   ;; Better idea:
   ;; store ?ruleset as nested maps with the following shape to facilitate more
   ;; efficient lookup:
   ;;    {?predicate_name: {?arity: ?sequence_of_rules}}
   ;; Note that this can still be inefficient as we will still perform repeated
   ;; computations when predicates with the same args are evaluated.
   ;; This can be addressed by tabled execution.
   ;; Also note that such recomputation will also arise in a naive transpilation
   ;; to JS/TS/any other lanugage, unless one involves memoization.
                        {:ruleset (m/and ?ruleset (m/scan (DECIDE ?goal IF ?body)))
                         :env ?env
                         :goals [?goal & ?goals]
                         :trace ?trace}
                        {:ruleset ?ruleset
                         :env ?env
                         :goals [?body & ?goals]
                         :trace ~(conj ?trace `(~?goal ~'⟹ ~?body))}))]
    state

   ;; TODO:
   ;; Instead of going into a deadlock when there are no applicable rules/facts,
   ;; consider asking the user for input and then transitioning based on that.

    ((r/choice
      (r/rewrite

   ;; Add metadata as edge to current trace, then refocus the abstract
   ;; machine to continue evaluation.
   ;;
   ;;   ⊢ ?env ok
   ;; ---------------------------------------------------------- [Tracing]
   ;;〈?ruleset, ?env, (TRACE ?goal PARENT ?parent) : ?goals, ?trace〉
   ;; ⟶ 〈?ruleset, ?env, ?goals ++ [?goal], (EDGE ?parent ?goal) : ?trace〉
       {:ruleset ?ruleset
        :env ?env
        :goals [(TRACE ?goal PARENT ?parent) & ?goals]
        :trace ?trace}
       {:ruleset ?ruleset
        :env ?env
        :goals [?goal & ?goals]
        :trace ~(conj ?trace `(~?parent ~'⟹ ~?goal))}

   ;;    ⊢ ?env ok
   ;; ---------------------------------------------------------- [Empty clause]
   ;; 〈?ruleset, ?env, TRUE : ?goals, ?trace〉⟶ 〈?ruleset, ?env, ?goals, ?trace〉
       {:ruleset ?ruleset :env ?env :goals [TRUE & ?goals] :trace ?trace}
       {:ruleset ?ruleset :env ?env :goals ?goals :trace ?trace}

   ;;  ⊢ ?env ok
   ;;  ⊢ ?goal = (?conjunct_0 AND ... AND ?conjunct_n)
   ;; ----------------------------------------------------------- [Conjunction]
   ;; 〈?ruleset, ?env, ?goal : ?goals, ?trace〉
   ;;  ⟶ 〈?ruleset, ?env,
   ;;      (TRACE ?conjunct_0 PARENT ?goal) : ... : (TRACE ?conjunct_n PARENT ?goal) : ?goals,
   ;;      ?trace〉
       {:ruleset ?ruleset
        :env ?env
        :goals [(m/and ?goal (?conjunct . AND !conjuncts ...)) & ?goals]
        :trace ?trace}
       {:ruleset ?ruleset
        :env ?env
        :goals [(TRACE ?conjunct PARENT ?goal) & [(TRACE !conjuncts PARENT ?goal) ...] & ?goals]
        :trace ?trace}

   ;;  ⊢ ?env ok
   ;;  ?goal' is a fresh variable not found in the head of any horn clause in ?ruleset
   ;;  ?goal = (?conjunct_0 OR ... OR ?conjunct_n)  
   ;; -------------------------------------------------------------------- [Disjunction]
   ;; 〈?ruleset, ?env, ?goal : ?goals, ?trace〉
   ;;  ⟶〈?ruleset, ?env,
   ;;     (TRACE (ASSERTZ (DECIDE ?goal' IF ?disjunct_0)) PARENT ?goal)
   ;;       : ... : (TRACE (ASSERTZ (DECIDE ?goal' IF ?disjunct_n)) PARENT ?goal)
   ;;       : ?goal' : (RETRACTALL ?goal') : ?goals,
   ;;     ?trace〉
       (m/and {:ruleset ?ruleset
               :env ?env
               :goals [(m/and ?goal (?disjunct . OR !disjuncts ...)) & ?goals]
               :trace ?trace}
              (m/let [?goal' (gensym "GOAL__")]))
       {:ruleset ?ruleset
        :env ?env
        :goals [(TRACE (ASSERTZ (DECIDE ?goal' IF ?disjunct)) PARENT ?goal) &
                [(TRACE (ASSERTZ (DECIDE ?goal' IF !disjuncts)) PARENT ?goal) ...] &
                [?goal' & [(RETRACTALL ?goal') & ?goals]]]
        :trace ?trace}

   ;;  ⊢ ?env ok
   ;; -------------------------------------------------------------------- [Assertz]
   ;; 〈?ruleset, ?env, (ASSERTZ ?rule) : ?goals, ?trace〉⟶〈?ruleset ∪ {?rule}, ?env, ?goals, ?trace〉
       {:ruleset ?ruleset :env ?env :goals [(ASSERTZ ?rule) & ?goals] :trace ?trace}
       {:ruleset ~(conj ?ruleset ?rule) :env ?env :goals ?goals :trace ?trace}

   ;; TODO
   ;;
   ;;   ⊢ ?env ok
   ;; -------------------------------------------------------------------- [Retractall]
   ;; 〈?ruleset, ?env, (RETRACTALL ?term) : ?goals, ?trace〉
   ;; ⟶〈{?rule ∈ ?ruleset | ∃ ?term' ≠ ?term, ∃ ?body, ?rule = (DECIDE ?term' IF ?body)},
   ;;    ?env, ?goals, ?trace〉
       {:ruleset ?ruleset :env ?env :goals [(RETRACTALL ?term) & ?goals] :trace ?trace}
       {:ruleset ?ruleset :env ?env :goals ?goals :trace ?trace}

   ;; TODO: Desugar IF p THEN ... ELSE ... assuming the decidability of the
   ;; excluded middle for p.

   ;; TODO: Implement negation as failure
   ;; Idea: Adapt the refocusing strategy which the call-by-value λμμ~ machine
   ;; uses to freeze the evaluation of a beta reduction to refocus to reduce
   ;; the argument first:
   ;; 1. Capture the current state of the machine in a continuation that is
   ;;    a suitably modified version of the μ~ construct and
   ;;    refocus to prove the formula that is being negated.
   ;; 2. Upon deadlock (ie deriving ⊥), throw to this
   ;;    continuation to continue evaluation.
   ;;
   ;;  ⊢ ?env ok
   ;; 〈?ruleset, ?env, [?term], ?trace〉⊨ AG (?goals ≠ [])
   ;; -------------------------------------------------------- [Negation as failure]
   ;; 〈?ruleset, ?env, (NOT ?term) : ?goals, ?trace〉⟶ 〈?ruleset, ?env, ?goals, ?trace〉
   ;;
   ;; Arithmetic (with unification handled appropriately)?
   ;; Idea: Separate possibly big-step evaluator for purely arithmetic exprs,
   ;; which tracks and propagates TRACE instructions appropriately.
   ;;
   ;; Higher-order and meta predicates like forall/2, findall/3, maplist, and
   ;; arithmetic one like min/max/sum/product?

   ;; Here we want to reflect ?var into a Meander variable which participates
   ;; in its unification process.
   ;; For ideas, see the Meander implementation of Datalog: https://github.com/noprompt/meander/blob/epsilon/examples/datascript.cljc
   ;; Seems like the trick here is to use compile-time metaprogramming via
   ;; macroexpand. Can we macroexpand in cljs at runtime?
   ;; Another possibility: Maybe use core.unify

   ;; TODO:
   ;; - Generalise the IS SUM construct below to support arbitrary functional
   ;;   exprs on RHS.
   ;; - Implement environment lookup.
   ;; - Desugar expression language into abstract machine.
   ;; - Annotate expressions with TRACE instructions for tracing.
   ;;
   ;;  ⊢ ?env ok               ?env ⊢ SUM ?xs ⇓ ?value
   ;; --------------------------------------------------------
   ;; 〈?ruleset, ?env, (?value IS SUM ?xs) : ?goals, ?trace〉
   ;;  ⟶ 〈?ruleset, ?env, ?goals, ?trace〉
   ;;
   ;;  ⊢ ?env ok               ?env ⊢ SUM ?xs ⇓ ?value
   ;; -----------------------------------------------------------
   ;; 〈?ruleset, ?env, (?variable IS SUM ?xs) : ?goals, ?trace〉
   ;;  ⟶ 〈?ruleset, ?env[?variable ↦ ?value], ?goals, ?trace〉
       {:ruleset ?ruleset
        :env ?env
        :goals [(m/and ?goal
                       (?term IS SUM
                              (m/app #(apply + %)
                                     (m/or (m/and ?term
                                                  (m/let [?number nil
                                                          ?env' ?env]))
                                           (m/and (m/not ?term)
                                                  (m/guard (not (number? ?term)))
                                                  ?number
                                                  (m/let [?env' (assoc ?env ?term ?number)]))))))
                & ?goals]
        :trace ?trace}
       {:ruleset ?ruleset
        :env ?env'
        :goals ?goals
        :trace ?trace})

   ;; TODO
   ;; To trace arithmetic exprs, can leverage the tracing facilities of the
   ;; abstract machine by desugaring nested operators like so: 
   ;;  x IS SUM (PRODUCT ...) ...
   ;;  => 
   ;;  y IS PRODUCT ...
   ;;  x IS SUM y ...
      (r/rewrite
       (m/and {:ruleset ?ruleset :env ?env :goals [?goal & ?goals] :trace ?trace}
              (m/guard (not (asked? ?goal)))
              (m/guard (= (js/prompt (str "Is it true that: " ?goal)) "yes"))
              (m/let [_ (add-asked! ?goal true)]))
       {:ruleset ?ruleset :env ?env
        :goals [(ASSERTZ (DECIDE ?goal IF TRUE)) & ?goals] :trace ?trace}

       (m/and ?state {:goals [?goal & _]} (m/let [_ (add-asked! ?goal false)]))
       ?state))
     state)))

#_(defn test! []
  (js/console.log
   (->> {:ruleset '#{(DECIDE p IF ((a AND b) OR c))
                     (DECIDE c IF TRUE)}
         :goals '[p]
         :trace []}
        step
        (mapv step)
        (mapv (partial mapv step)) ffirst first
        step first
        step first
        step first
        step
        (mapv step))))

#_(defn test! []
  (js/console.log
   (->> {:ruleset '[(DECIDE p IF (q OR (x IS SUM [0 1 2])))]
         :env {}
         :goals '[p]
         :trace []}
        (#(do (js/console.log "Initial configuration: " %) %))
        step first
        step first
        step first
        step first
        step first
        step first
        step
        #_((fn [[x y]] [x (first (step y))]))
        #_((fn [[x y]] [x (first (step y))]))
        )))

#_(defn test! []
  (js/console.log
   (->> {:ruleset '[(DECIDE p IF a)]
         :env {}
         :goals '[p]
         :trace []}
        step
        first
        step
        ))
  (js/console.log "Asked: " @asked))

(defsession clara-session
  'l4-rule-engine.clara)

(defn test! []
  (-> clara-session
      (insert (->Edge 0 1) (->Edge 1 2))
      (fire-rules)
      ;; session->fact-graph
      ;; inspect
      explain-activations
      js/console.log))