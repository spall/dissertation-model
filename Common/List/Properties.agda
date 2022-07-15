module Common.List.Properties where

open import Agda.Builtin.Equality
open import Data.List using (List ; _++_ ; [_] ; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Product using (∃-syntax ; _,_ ; _×_)
open import Data.List.Categorical using (monad)
open import Category.Monad using (RawMonad)
open import Level using (Level)

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

  variable
    ℓ : Level
    A : Set ℓ
    B : Set ℓ

_before_∈_ : A -> A -> List A -> Set _ -- why the _ ?
v before w ∈ xs = ∃[ ys ](∃[ zs ](xs ≡ ys ++ [ v ] ++ zs × w ∈ zs))

before-∷ : ∀ (v w x : A) xs → v before w ∈ xs → v before w ∈ (x ∷ xs)
before-∷ v w x xs (as , bs , xs≡as++v∷bs , w∈bs) = x ∷ as , bs , cong (x ∷_) xs≡as++v∷bs , w∈bs

