(ns l4-rule-engine.tuprolog-kt
  (:require ["@tuprolog/2p-core" :as tu-prolog-core]
            ["@tuprolog/2p-solve" :as tu-prolog-solve]
            ["@tuprolog/2p-solve-classic" :as tu-prolog-solve-classic]
            ["@tuprolog/2p-theory" :as tu-prolog-theory]
            ["@tuprolog/2p-parser-core" :as tu-prolog-parser-core]
            ["@tuprolog/2p-parser-theory" :as tu-prolog-parser-theory]
            [applied-science.js-interop :as jsi]))

;; References:
;; https://github.com/tuProlog/2p-kt
;; https://github.com/tuProlog/2p-kt-playground
;; https://github.com/tuProlog/arg2p-kt-web
;; https://github.com/tuProlog/2pkt-problog-compatibility-demo/tree/master/js 
;;
;; https://github.com/tuProlog/2p-kt-presentation/releases/tag/1.2.0-2021-06-28T100324
;; https://amslaurea.unibo.it/19444/1/2p_kt.pdf
;; https://amslaurea.unibo.it/24958/1/thesis_giordano.pdf

(defn- ->tuprolog-mod [tu-prolog-mod & kws]
  (->> kws
       (concat [:it :unibo :tuprolog])
       (jsi/get-in tu-prolog-mod)))

(def tu-prolog
  (->tuprolog-mod tu-prolog-core))

(def solve
  (->tuprolog-mod tu-prolog-solve :solve))

(def classic
  (->tuprolog-mod tu-prolog-solve-classic :solve :classic))

(def theory
  (->tuprolog-mod tu-prolog-theory :theory))

(def core-parsing
  (->tuprolog-mod tu-prolog-parser-core :core :parsing))

(def theory-parsing
  (->tuprolog-mod tu-prolog-parser-theory :theory :parsing))

(jsi/assoc-in! tu-prolog [:core :parsing] core-parsing)
(jsi/assoc! theory :parsing theory-parsing)

(jsi/assoc! tu-prolog :theory theory)
(jsi/assoc! tu-prolog :solve solve)
(jsi/assoc! tu-prolog :classic classic)

(js/console.log tu-prolog)

#_(def query
  (->> "person(X)"
       (jsi/call-in tu-prolog [:core :parsing :parseStringAsStruct])))

(def query
  (let [scope (jsi/call-in tu-prolog [:core :Scope :Companion :empty])]
    (jsi/call scope :structOf
              "path"
              #js [(jsi/call scope :varOf "X") (jsi/call scope :varOf "Y")])))

(def program
  (->> "edge(0, 1).
        edge(1, 2).
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- edge(X, Z), path(Z,  Y)."
       (jsi/call-in tu-prolog [:theory :parsing :parseAsTheory])))

#_(js/console.log "Program: " program)

#_(-> tu-prolog
    (jsi/get-in [:classic :ClassicSolverFactory])
    (js/console.log))

(def solver
  (let [classic-solver-factory (jsi/get-in tu-prolog
                                           [:classic :ClassicSolverFactory])
        solver (jsi/call classic-solver-factory :mutableSolverOf)]
    (jsi/call solver :loadStaticKb program)
    solver))

(def solutions
  (jsi/call solver :solveList query))

(-> solutions
    str
    ;; es6-iterator-seq
    (js/console.log))

#_(js/console.log "Solver: " solver)

(def current-context
  (jsi/get solver :currentContext))

(js/console.log "Current solver context: " current-context)

(-> current-context
    (jsi/get-in [:logicStackTrace])
    str
    #_(jsi/call :toArray)
    (js/console.log))