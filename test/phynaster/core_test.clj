(ns phynaster.core-test
  (:require [clojure.test :refer :all]
            [phynaster.core :refer :all]))

(defmacro $ [expr value doc]
  `(is (= ~expr ~value) ~doc))
