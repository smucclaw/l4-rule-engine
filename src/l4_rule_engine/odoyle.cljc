(ns l4-rule-engine.odoyle
  (:require [odoyle.rules :as odoyle]))

(def rules
  (odoyle/ruleset
   {::path
    [:what [:or
            [::edge source target]
            [:and [::edge source target'] [::path target' target]]]
     :then (odoyle/insert! ::path source target)]}))