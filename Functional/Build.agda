open import Functional.State using (Oracle ; Cmd ; FileSystem)

module Functional.Build (oracle : Oracle) where

open import Data.List using (List ; [] ; _∷_)
open import Functional.State.Helpers (oracle) using (cmdReadNames ; cmdWriteNames ; run)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.Product using (_×_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)

Build : Set
Build = List Cmd

UniqueEvidence : Build → Build → List Cmd → Set
UniqueEvidence b₁ b₂ ls = Unique b₁ × Unique b₂ × Unique ls × Disjoint b₁ ls

data DisjointBuild : FileSystem → Build → Set where
  []  : ∀ {s} → DisjointBuild s []
  _∷_ : ∀ {s} {x} {b} → Disjoint (cmdReadNames x s) (cmdWriteNames x s) →
      DisjointBuild (run x s) b → DisjointBuild s (x ∷ b)

PreCond : FileSystem → Build → Build → Set
PreCond s br bc = DisjointBuild s br × Unique br × Unique bc × bc ↭ br
