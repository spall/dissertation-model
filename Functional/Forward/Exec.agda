open import Functional.State using (State ; Oracle ; Cmd ; FileSystem ; Memory ; save)

module Functional.Forward.Exec (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) as St using (cmdReadNames)
open import Data.Bool using (Bool ; if_then_else_)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.String.Properties using (_≟_)
open import Data.Maybe as Maybe using (Maybe ; decToMaybe ; is-nothing)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Product using (proj₁ ; _,_ ; _×_)
open import Functional.File using (FileName ; FileContent)
open import Functional.Build (oracle) using (Build)
open import Data.List.Relation.Unary.Any using (tail)
open import Data.List.Relation.Unary.All as All using (All ; all?)
open import Relation.Binary.PropositionalEquality using (decSetoid)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_)
open import Relation.Nullary using (yes ; no ; Dec)

maybeAll : {sys : FileSystem} → (ls : List (FileName × Maybe FileContent)) →
         Maybe (All (λ (f₁ , v₁) → sys f₁ ≡ v₁) ls)
maybeAll {sys} ls = decToMaybe (g₁ ls)
  where g₁ : (ls : List (FileName × Maybe FileContent)) →
           Dec (All (λ (f₁ , v₁) → sys f₁ ≡ v₁) ls)
        g₁ ls = all? (λ (f₁ , v₁) → ≡-dec _≟_ (sys f₁) v₁) ls

get : (x : Cmd) → (ls : Memory) → x ∈ map proj₁ ls →
    List (FileName × Maybe FileContent)
get x ((x₁ , fs) ∷ ls) x∈ with x ≟ x₁
... | yes x≡x₁ = fs
... | no ¬x≡x₁ = get x ls (tail ¬x≡x₁ x∈)

run? : Cmd → State → Bool
run? x (s , m) with x ∈? map proj₁ m
... | no x∉ = Bool.true
... | yes x∈ = is-nothing (maybeAll {s} (get x m x∈))

-- save extends the Memory with a new entry
doRun : State → Cmd → State
doRun (s , m) x = let s₂ = St.run x s in
                   (s₂ , save x (cmdReadNames x s) s₂ m)

runF : Cmd → (FileSystem × Memory) → (FileSystem × Memory)
runF cmd st = if (run? cmd st)
               then doRun st cmd
               else st

fabricate : Build → (FileSystem × Memory) → (FileSystem × Memory)
fabricate [] st = st
fabricate (x ∷ b) st = fabricate b (runF x st)
