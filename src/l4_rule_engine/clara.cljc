(ns l4-rule-engine.clara
  (:require [clara.rules :refer [defrule insert!]]))

(defrecord Edge [source target])

(defrecord Path [source target])

;; (defrule path-base
;;   [Edge (= ?source source) (= ?target target)]
;;   =>
;;   (insert! (->Path ?source ?target)))

(defrule path
  [:or
   [Edge (= ?source source) (= ?target target)]
   [:and
    [Edge (= ?source source) (= ?target' target)]
    [Path (= ?target' source) (= ?target target)]]]
  =>
  (insert! (->Path ?source ?target)))