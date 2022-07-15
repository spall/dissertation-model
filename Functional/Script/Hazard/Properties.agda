open import Functional.State using (Oracle ; Cmd)

module Functional.Script.Hazard.Properties (oracle : Oracle) where
open import Functional.State.Properties (oracle)
  using (run-cong₂-File ; run-unchanged-File)
open import Functional.State.Helpers (oracle)
  using (run ; cmdWriteNames ; cmdReadNames)
open import Functional.Script.Exec (oracle)
  using (script ; buildReadNames ; buildWriteNames)
open import Functional.Build (oracle) using (Build)
open import Common.List.Properties using (_before_∈_)
open import Agda.Builtin.Equality
open import Functional.File using (FileName)
open import Functional.Script.Hazard.Base (oracle)
  using (HazardFree ; [] ; _∷_ ; files ; cmdsRun ; cmdWrote ; FileInfo ; save ; filesRead
  ; Hazard ; Speculative ; ReadWrite ; WriteWrite ; cmdRead ; filesWrote) 
open import Data.List as L
  using (_∷_ ; _++_ ; map ; foldr ; List ; foldl ; _∷ʳ_ ; [] ; reverse ; [_] ; concatMap
  ; concat)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; _×_ ; Σ-syntax ; ∃-syntax ; map₁)
open import Relation.Binary.PropositionalEquality
  using (subst ; subst₂ ; cong ; sym ; trans ; cong₂)
open import Function using (_∘_)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.String using (String)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.List.Properties
  using (map-++-commute ; ++-assoc ; reverse-involutive ; ∷-injectiveˡ ; ∷-injectiveʳ
  ; reverse-++-commute ; unfold-reverse ; ++-identityˡ ; concat-++)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Unary.Any.Properties using (reverse⁺ ; reverse⁻)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec)
open import Data.Bool using (true ; false)

-- helper lemmas --

-- if there is a file in the cmdRead for x , then x ∈ xs
lemma1 : ∀ {v} x xs → v ∈ cmdRead xs x → x ∈ map proj₁ xs
lemma1 x (x₁ ∷ xs) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = here (sym x₁≡x)
... | no ¬x₁≡x = there (lemma1 x xs v∈)

-- if there is a file in the cmdwrote for x , then x ∈ xs
lemma2 : ∀ {v} x xs → v ∈ cmdWrote xs x → x ∈ map proj₁ xs
lemma2 x (x₁ ∷ xs) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = here (sym x₁≡x)
... | no ¬x₁≡x = there (lemma2 x xs v∈)

lemma3 : ∀ {s} {x} {ls} → Disjoint (cmdWriteNames x s) ls →
       (∀ f₁ → f₁ ∈ ls → run x s f₁ ≡ s f₁)
lemma3 {s} {x} dsj f₁ f₁∈ls with f₁ ∈? cmdWriteNames x s
... | yes f₁∈ = contradiction (f₁∈ , f₁∈ls) dsj
... | no f₁∉ = sym (run-unchanged-File f₁ (proj₂ (proj₁ (oracle x) s)) f₁∉)

g₂ : ∀ {x : Cmd} xs → x ∉ xs → All (λ y → ¬ x ≡ y) xs
g₂ [] x∉xs = All.[]
g₂ (x ∷ xs) x∉xs = (λ x₃ → x∉xs (here x₃)) All.∷ (g₂ xs λ x₃ → x∉xs (there x₃))

g₃ : ∀ {x} {b₁} (ys : Build) {xs} {x₁} {x₂} → x ∷ b₁ ≡ ys ∷ʳ x₁ ++ xs → x₂ ∈ ys →
   x₁ ∈ b₁
g₃ (x ∷ ys) ≡₁ x₂∈ys
  = subst (λ x₄ → _ ∈ x₄) (sym (∷-injectiveʳ ≡₁)) (∈-++⁺ˡ (∈-++⁺ʳ ys (here refl)))

g₄ : ∀ {x : Cmd} {x₁} {ls} → x ∈ ls → x₁ ∉ ls → ¬ x ≡ x₁
g₄ x∈ls x₁∉ls = λ x≡x₁ → x₁∉ls (subst (λ x₄ → x₄ ∈ _) x≡x₁ x∈ls)

g₅ : ∀ (x : Cmd) ys → All (λ y → ¬ x ≡ y) ys → x ∉ ys
g₅ x [] All.[] = λ ()
g₅ x (x₁ ∷ ys) (¬x≡x₁ All.∷ all₁) x∈x₁∷xs = g₅ x ys all₁ (tail ¬x≡x₁ x∈x₁∷xs)

-- lemmas about builds and hazards -- 

∈-concatMap-++ : ∀ {v : FileName} f (xs : FileInfo) ys zs →
               v ∈ concatMap f (xs ++ zs) → v ∈ concatMap f (xs ++ ys ++ zs)
∈-concatMap-++ f xs ys zs v∈ with
  ∈-++⁻ (concat (map f xs)) (subst (λ x → _ ∈ x) ≡₁ v∈)
  where ≡₁ : concatMap f (xs ++ zs) ≡ concat (map f xs) ++ concat (map f zs)
        ≡₁ = trans (cong concat (map-++-commute f xs zs))
                   (sym (concat-++ (map f xs) (map f zs)))
... | inj₁ v∈xs = subst (λ x → _ ∈ x) ≡₁ (∈-++⁺ˡ v∈xs)
  where ≡₁ : concat (map f xs) ++ concat (map f (ys ++ zs)) ≡
             concat (map f (xs ++ ys ++ zs))
        ≡₁ = trans (concat-++ (map f xs) (map f (ys ++ zs)))
                   (cong concat (sym (map-++-commute f xs (ys ++ zs))))
... | inj₂ v∈ys
  = subst (λ x → _ ∈ x) ≡₁
          (∈-++⁺ʳ (concat (map f xs)) (∈-++⁺ʳ (concat (map f ys)) v∈ys))
  where ≡₁ : concat (map f xs) ++ concat (map f ys) ++ concat (map f zs) ≡
             concat (map f (xs ++ ys ++ zs))
        ≡₁ = trans (cong (concat (map f xs) ++_) (concat-++ (map f ys) (map f zs)))
                   (trans (concat-++ (map f xs) (map f ys ++ map f zs))
                          (cong concat
                                (trans (cong (map f xs ++_)
                                       (sym (map-++-commute f ys zs)))
                                       (sym (map-++-commute f xs (ys ++ zs))))))

∈-cmdRead∷l : ∀ {v} x ls → v ∈ proj₁ (proj₂ x) → v ∈ cmdRead (x ∷ ls) (proj₁ x)
∈-cmdRead∷l x ls v∈ with (proj₁ x) ≟ (proj₁ x)
... | no ¬x≡x = contradiction refl ¬x≡x
... | yes x≡x = v∈

∈-filesWrote-++ : ∀ {v} xs ys zs → v ∈ filesWrote (xs ++ zs) →
                v ∈ filesWrote (xs ++ ys ++ zs)
∈-filesWrote-++ = ∈-concatMap-++ (proj₂ ∘ proj₂)

∈-cmdRead++⁺ʳ : ∀ {v} x xs ys → Unique (map proj₁ (xs ++ ys)) →
             v ∈ cmdRead ys x → v ∈ cmdRead (xs ++ ys) x
∈-cmdRead++⁺ʳ x [] ys u v∈ = v∈
∈-cmdRead++⁺ʳ x (x₁ ∷ xs) ys (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = contradiction x₁≡x (lookup px₁ x∈xs++ys)
  where x∈xs++ys : x ∈ map proj₁ (xs ++ ys)
        x∈xs++ys = subst (λ ls → _ ∈ ls) (sym (map-++-commute proj₁ xs ys))
                         (∈-++⁺ʳ (map proj₁ xs) (lemma1 x ys v∈))
... | no ¬x₁≡x = ∈-cmdRead++⁺ʳ x xs ys u v∈

∈-cmdRead++mid : ∀ {v} x xs ys zs → Unique (map proj₁ (xs ++ ys ++ zs)) →
               v ∈ cmdRead (xs ++ zs) x → v ∈ cmdRead (xs ++ ys ++ zs) x
∈-cmdRead++mid x [] ys zs u v∈ = ∈-cmdRead++⁺ʳ x ys zs u v∈
∈-cmdRead++mid x (x₁ ∷ xs) ys zs (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = v∈
... | no ¬x₁≡x = ∈-cmdRead++mid x xs ys zs u v∈

cmdWrote∷-≡ : ∀ x ls → cmdWrote (x ∷ ls) (proj₁ x) ≡ proj₂ (proj₂ x)
cmdWrote∷-≡ x ls with (proj₁ x) ≟ (proj₁ x)
... | yes x≡x = refl
... | no ¬x≡x = contradiction refl ¬x≡x

∈-cmdWrote∷l : ∀ {v} x ls → v ∈ proj₂ (proj₂ x) → v ∈ cmdWrote (x ∷ ls) (proj₁ x)
∈-cmdWrote∷l x ls v∈ with (proj₁ x) ≟ (proj₁ x)
... | no ¬x≡x = contradiction refl ¬x≡x
... | yes x≡x = v∈

∈-cmdWrote∷ : ∀ {v} x x₁ ls → v ∈ cmdWrote ls x₁ → ¬ (proj₁ x) ≡ x₁ →
            v ∈ cmdWrote (x ∷ ls) x₁
∈-cmdWrote∷ x x₁ ls v∈ ¬≡ with (proj₁ x) ≟ x₁
... | yes x≡x₁ = contradiction x≡x₁ ¬≡
... | no ¬x≡x₁ = v∈

∈-cmdWrote++⁺ʳ : ∀ {v} x xs ys → Unique (map proj₁ (xs ++ ys)) →
              v ∈ cmdWrote ys x → v ∈ cmdWrote (xs ++ ys) x
∈-cmdWrote++⁺ʳ x [] ys u v∈ = v∈
∈-cmdWrote++⁺ʳ x (x₁ ∷ xs) ys (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = contradiction x₁≡x (lookup px₁ x∈xs++ys)
  where x∈xs++ys : x ∈ map proj₁ (xs ++ ys)
        x∈xs++ys = subst (λ ls → _ ∈ ls) (sym (map-++-commute proj₁ xs ys))
                         (∈-++⁺ʳ (map proj₁ xs) (lemma2 x ys v∈))
... | no ¬x₁≡x = ∈-cmdWrote++⁺ʳ x xs ys u v∈

∈-cmdWrote++mid : ∀ {v} x xs ys zs → Unique (map proj₁ (xs ++ ys ++ zs)) →
                v ∈ cmdWrote (xs ++ zs) x → v ∈ cmdWrote (xs ++ ys ++ zs) x
∈-cmdWrote++mid x [] ys zs u v∈ = ∈-cmdWrote++⁺ʳ x ys zs u v∈
∈-cmdWrote++mid x (x₁ ∷ xs) ys zs (px₁ ∷ u) v∈ with (proj₁ x₁) ≟ x
... | yes x₁≡x = v∈
... | no ¬x₁≡x = ∈-cmdWrote++mid x xs ys zs u v∈

∈-filesRead-++ : ∀ {v} xs ys zs → v ∈ filesRead (xs ++ zs) →
               v ∈ filesRead (xs ++ ys ++ zs)
∈-filesRead-++ = ∈-concatMap-++ (proj₁ ∘ proj₂)

¬bf-∷ʳ : ∀ (x : Cmd) x₁ {x₂} b₁ → ¬ x₂ ≡ x → ¬ x₁ before x₂ ∈ b₁ →
       ¬ x₁ before x₂ ∈ (b₁ ∷ʳ x)
¬bf-∷ʳ x x₁ {x₂} b₁ ¬x₂≡x ¬bf (xs , ys , b₁∷ʳx≡xs++x₁∷ys , x₂∈ys) with
  g₁ (reverse b₁) (reverse ys) (reverse xs) x₂ x x₁ ≡₁ (reverse⁺ x₂∈ys) ¬x₂≡x
    where g₁ : ∀ b₁ ys xs x₂ x x₁ → x ∷ b₁ ≡ ys ∷ʳ x₁ ++ xs → x₂ ∈ ys →
             ¬ x₂ ≡ x → ∃[ zs ](b₁ ≡ zs ∷ʳ x₁ ++ xs × x₂ ∈ zs)
          g₁ b₁ (x₃ ∷ ys) xs x₂ x x₁ ≡₁ x₂∈ys ¬x₂≡x
            = ys , ∷-injectiveʳ ≡₁ ,
              tail (λ x₂≡x₃ → ¬x₂≡x (trans x₂≡x₃ (sym (∷-injectiveˡ ≡₁)))) x₂∈ys
          ≡₁ : x ∷ reverse b₁ ≡ reverse ys ∷ʳ x₁ ++ reverse xs
          ≡₁ = trans (sym (reverse-++-commute b₁ (x ∷ [])))
                     (trans (cong reverse b₁∷ʳx≡xs++x₁∷ys)
                            (trans (reverse-++-commute xs (x₁ ∷ ys))
                                   (cong (_++ reverse xs) (unfold-reverse x₁ ys))))
... | zs , ≡₃ , x₂∈zs = ¬bf (xs , reverse zs , ≡₂ , reverse⁺ x₂∈zs)
  where ≡₂ : b₁ ≡ xs ++ x₁ ∷ reverse zs
        ≡₂ = trans (sym (reverse-involutive b₁))
                   (trans (cong reverse ≡₃)
                          (trans (reverse-++-commute (zs ∷ʳ x₁) (reverse xs))
                                 (cong₂ _++_ (reverse-involutive xs)
                                        (reverse-++-commute zs (x₁ ∷ [])))))

unique→¬≡ : ∀ ls (x₁ : Cmd) {x} → x₁ ∈ ls → Unique (ls ∷ʳ x) → ¬ x₁ ≡ x
unique→¬≡ (x ∷ ls) x₁ x₁∈ls (px ∷ u) with x₁ ≟ x
... | yes x₁≡x
  = λ x₁≡x₂ → lookup px (∈-++⁺ʳ ls (here refl)) (trans (sym x₁≡x) x₁≡x₂)
unique→¬≡ (x ∷ ls) x₁ x₁∈ls (px ∷ u) | no ¬x₁≡x
  = unique→¬≡ ls x₁ (tail ¬x₁≡x x₁∈ls) u

¬hz-∷ʳ-r : ∀ {s} {x} {b} {x₁} {ls} → Unique (b ∷ʳ x₁) → ¬ Hazard s x (b ∷ʳ x₁) ls →
         ¬ Hazard s x b ls
¬hz-∷ʳ-r u ¬hz (Speculative x₀ x₂ y x₃ x₄ x₅ x₆)
  = ¬hz (Speculative x₀ x₂ y (∈-++⁺ˡ x₃) (¬bf-∷ʳ _ _ _ (unique→¬≡ _ _ x₃ u) x₄)
                     x₅ x₆)
¬hz-∷ʳ-r u ¬hz (ReadWrite x x₁) = ¬hz (ReadWrite x x₁)
¬hz-∷ʳ-r u ¬hz (WriteWrite x x₁) = ¬hz (WriteWrite x x₁)

hf-∷ʳ-r : ∀ {s} b₁ b₂ {x} {ls} → Unique (b₂ ∷ʳ x) → HazardFree s b₁ (b₂ ∷ʳ x) ls →
        HazardFree s b₁ b₂ ls
hf-∷ʳ-r [] b₂ u hf = []
hf-∷ʳ-r (x ∷ b₁) b₂ u (¬hz ∷ hf)
  = (¬hz-∷ʳ-r u ¬hz) ∷ (hf-∷ʳ-r b₁ b₂ u hf)

before-add-mid : ∀ x₂ x₁ (xs : Build) ys zs → x₂ before x₁ ∈ (xs ++ zs) →
               x₂ before x₁ ∈ (xs ++ ys ++ zs)
before-add-mid x₂ x₁ [] ys zs (as , bs , zs≡as++x₂∷bs , x₁∈bs)
  = ys ++ as , bs , ≡₁ , x₁∈bs
    where ≡₁ : ys ++ zs ≡ (ys ++ as) ++ x₂ ∷ bs
          ≡₁ = trans (cong (ys ++_) zs≡as++x₂∷bs) (sym (++-assoc ys as (x₂ ∷ bs)))
before-add-mid x₂ x₁ (x ∷ xs) ys zs ([] , bs , x∷xs++zs≡x₂∷bs , x₁∈bs)
  = [] , xs ++ ys ++ zs , cong (_∷ xs ++ ys ++ zs) (∷-injectiveˡ x∷xs++zs≡x₂∷bs) , ∈₁
    where ∈₁ : x₁ ∈ xs ++ ys ++ zs
          ∈₁ with ∈-++⁻ xs (subst (λ x₃ → x₁ ∈ x₃)
                                  (sym (∷-injectiveʳ x∷xs++zs≡x₂∷bs)) x₁∈bs)
          ... | inj₁ x₁∈xs = ∈-++⁺ˡ x₁∈xs
          ... | inj₂ x₁∈zs = ∈-++⁺ʳ xs (∈-++⁺ʳ ys x₁∈zs)
before-add-mid x₂ x₁ (x ∷ xs) ys zs (x₃ ∷ as , bs , x∷xs++zs≡x₃∷as++x₂∷bs , x₁∈bs) with
  before-add-mid x₂ x₁ xs ys zs (as , bs , ∷-injectiveʳ x∷xs++zs≡x₃∷as++x₂∷bs , x₁∈bs)
... | cs , ds , xs++ys≡cs++x₂∷ds , x₁∈ds
  = x ∷ cs , ds , cong (x ∷_) xs++ys≡cs++x₂∷ds , x₁∈ds

¬Hazard-drop-mid : ∀ {s} {x} {b₂} xs ys zs →
                 Unique (x ∷ cmdsRun (xs ++ ys ++ zs)) →
                 ¬ Hazard s x b₂ (xs ++ ys ++ zs) → ¬ Hazard s x b₂ (xs ++ zs)
¬Hazard-drop-mid xs ys zs u ¬hz (ReadWrite x x₁)
  = ¬hz (ReadWrite x (∈-filesRead-++ xs ys zs x₁))
¬Hazard-drop-mid xs ys zs u ¬hz (WriteWrite x x₁)
  = ¬hz (WriteWrite x (∈-filesWrote-++ xs ys zs x₁))
¬Hazard-drop-mid {s} {x} xs ys zs u ¬hz (Speculative x₁ x₂ y x₃ x₄ x₅ x₆)
  = ¬hz (Speculative x₁ x₂ bf x₃ x₄ (∈-cmdRead++mid x₂ (save s x xs) ys zs u x₅)
                     (∈-cmdWrote++mid x₁ (save s x xs) ys zs u x₆))
    where bf₁ : x₂ before x₁ ∈ (x ∷ cmdsRun xs ++ cmdsRun zs)
          bf₁ = subst (λ x₇ → x₂ before x₁ ∈ x₇)
                      (cong (x ∷_) (map-++-commute proj₁ xs zs)) y
          bf : x₂ before x₁ ∈ (x ∷ cmdsRun (xs ++ ys ++ zs))
          bf with
            (before-add-mid x₂ x₁ (x ∷ cmdsRun xs) (cmdsRun ys) (cmdsRun zs) bf₁)
          ... | a
            = subst (λ x₇ → x₂ before x₁ ∈ x₇)
                    (sym (trans (cong (x ∷_) (map-++-commute proj₁ xs (ys ++ zs)))
                                (cong ((x ∷ (map proj₁ xs)) ++_)
                                      (map-++-commute proj₁ ys zs)))) a

hazard-still : ∀ {s} {s₁} {x} {b} {ls} → proj₁ (oracle x) s ≡ proj₁ (oracle x) s₁ →
             Hazard s x b ls → Hazard s₁ x b ls
hazard-still ≡₁ (ReadWrite x x₁)
  = ReadWrite (subst (λ x₃ → _ ∈ x₃) (cong (map proj₁ ∘ proj₂) ≡₁) x) x₁
hazard-still ≡₁ (WriteWrite x x₁)
  = WriteWrite (subst (λ x₃ → _ ∈ x₃) (cong (map proj₁ ∘ proj₂) ≡₁) x) x₁
hazard-still {s} {s₁} {x} ≡₁ (Speculative {s} {x} {b} {ls} {v} x₁ x₂ y x₃ x₄ x₅ x₆)
  = Speculative x₁ x₂ y x₃ x₄ (subst (λ x₈ → v ∈ cmdRead x₈ x₂) (cong (_∷ _) ≡₂) x₅)
    (subst (λ x₈ → v ∈ cmdWrote x₈ x₁) (cong (_∷ _) ≡₂) x₆)
    where ≡₂ : (x , cmdReadNames x s , cmdWriteNames x s) ≡
             (x , cmdReadNames x s₁ , cmdWriteNames x s₁)
          ≡₂ = cong (x ,_) (cong₂ _,_ (cong (map proj₁ ∘ proj₁) ≡₁)
                                      (cong (map proj₁ ∘ proj₂) ≡₁))
 

hf-still : ∀ {s₁} {s} b₁ {b₂} xs ys zs →
         (∀ f₁ → f₁ ∈ buildReadNames s₁ b₁ → s₁ f₁ ≡ s f₁) → Unique b₁ →
         Unique (map proj₁ (xs ++ ys ++ zs)) →
         Disjoint b₁ (map proj₁ (xs ++ ys ++ zs)) →
         HazardFree s₁ b₁ b₂ (xs ++ ys ++ zs) →
         HazardFree s b₁ b₂ (xs ++ zs)
hf-still [] xs ys zs ∀₁ ub₁ u dsj hf = []
hf-still {s₁} {s} (x ∷ b₁) xs ys zs ∀₁ (px ∷ ub₁) u dsj (¬hz ∷ hf)
  = ¬hz₁ ∷ (hf-still b₁ (save s x xs) ys zs ∀₂ ub₁ u₂ dsj₁ hf₂) 
    where dsj₁ : Disjoint b₁ (x ∷ map proj₁ (xs ++ ys ++ zs))
          dsj₁ = λ x₁ → dsj (there (proj₁ x₁) ,
                 tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
          ≡₀ : proj₁ (oracle x) s₁ ≡ proj₁ (oracle x) s
          ≡₀ = (proj₂ (oracle x) s₁ s λ f₁ x₃ → ∀₁ f₁ (∈-++⁺ˡ x₃))
          ≡₁ : cmdWriteNames x s₁ ≡ cmdWriteNames x s
          ≡₁ = cong (map proj₁ ∘ proj₂) ≡₀
          ≡₂ : cmdReadNames x s₁ ≡ cmdReadNames x s
          ≡₂ = cong (map proj₁ ∘ proj₁) ≡₀
          hf₂ : HazardFree (run x s₁) b₁ _
                 ((x , cmdReadNames x s , cmdWriteNames x s) ∷ xs ++ ys ++ zs)
          hf₂ = subst (λ x₃ → HazardFree (run x s₁) b₁ _ (x₃ ∷ xs ++ ys ++ zs))
                      (cong (x ,_) (cong₂ _,_ ≡₂ ≡₁)) hf
          ∀₂ : ∀ f₁ → f₁ ∈ buildReadNames (run x s₁) b₁ → run x s₁ f₁ ≡ run x s f₁
          ∀₂ f₁ f₁∈ with ∀₁ f₁ (∈-++⁺ʳ (cmdReadNames x s₁) f₁∈)
          ... | s₁f₁≡sf₁ = run-cong₂-File ≡₀ s₁f₁≡sf₁
          u₂ : Unique (x ∷ (map proj₁ (xs ++ ys ++ zs)))
          u₂ = (g₂ (map proj₁ (xs ++ ys ++ zs)) λ x₁ → dsj (here refl , x₁)) ∷ u
          ¬hz₁ : ¬ Hazard s x _ (xs ++ zs)
          ¬hz₁ hz with ¬Hazard-drop-mid xs ys zs u₂ ¬hz
          ... | a = a (hazard-still (sym ≡₀) hz)

hf=>disjoint-∷ʳ : ∀ {s} {x} ys {b₁} {ls} → x ∉ ys → ys ⊆ (b₁ ∷ʳ x) →
                Unique (b₁ ∷ʳ x) → HazardFree s ys (b₁ ∷ʳ x) ls →
                Disjoint (cmdWrote ls x) (buildReadNames s ys)
hf=>disjoint-∷ʳ [] x∉ys ⊆₁ u [] = λ ()
hf=>disjoint-∷ʳ {s} {x} (x₃ ∷ b₂) {b₁} x∉ys ⊆₁ u (¬hz ∷ hf) x₄ with
  ∈-++⁻ (cmdReadNames x₃ s) (proj₂ x₄)
... | inj₁ v∈₁ = ¬hz (Speculative x x₃ ([] , map proj₁ _ , refl , lemma2 x _ (proj₁ x₄))
                       (⊆₁ (here refl)) ¬bf (∈-cmdRead∷l x₃i _ v∈₁)
                       (∈-cmdWrote∷ x₃i x _ (proj₁ x₄) (g₄ (here refl) x∉ys)))
  where x₃i : (Cmd × List FileName × List FileName)
        x₃i = (x₃ , (cmdReadNames x₃ s) , (cmdWriteNames x₃ s))
        ¬bf : ¬ x before x₃ ∈ (_ ∷ʳ x)
        ¬bf (xs , ys , b₁∷ʳx≡xs++x∷ys , x₃∈ys)
          = contradiction refl
              (unique→¬≡ b₁ x (reverse⁻ (g₃ (reverse ys) ≡₂ (reverse⁺ x₃∈ys))) u)
          where ≡₂ : x ∷ reverse b₁ ≡ reverse ys ∷ʳ x ++ reverse xs
                ≡₂ = trans (sym (reverse-++-commute b₁ [ x ]))
                           (trans (cong reverse b₁∷ʳx≡xs++x∷ys)
                                  (trans (reverse-++-commute xs (x ∷ ys))
                                         (cong (_++ reverse xs)
                                               (unfold-reverse x ys))))
... | inj₂ v∈₂ = (hf=>disjoint-∷ʳ b₂ (λ x₁ → x∉ys (there x₁)) (λ x₁ → ⊆₁ (there x₁)) u hf)
                 (∈-cmdWrote∷ x₃i x _ (proj₁ x₄) (g₄ (here refl) x∉ys) , v∈₂)
  where x₃i : (Cmd × List FileName × List FileName)
        x₃i = (x₃ , (cmdReadNames x₃ s) , (cmdWriteNames x₃ s))

-- we need to know x doesnt write to anything read by ys a command in ys.
-- we should know this from the ¬ speculative hazard info and ?
hf-drop-mid : ∀ {s} xs ys b₁ {x} {ls} → xs ++ x ∷ ys ⊆ b₁ ∷ʳ x →
            Unique (xs ++ x ∷ ys) → Unique (b₁ ∷ʳ x) → Unique (map proj₁ ls) →
            Disjoint (xs ++ x ∷ ys) (map proj₁ ls) →
            HazardFree s (xs ++ x ∷ ys) (b₁ ∷ʳ x) ls → HazardFree s (xs ++ ys) b₁ ls
hf-drop-mid {s} List.[] List.[] b₁ ⊆₁ u₁ u uls dsj hf = []
hf-drop-mid {s} List.[] ys b₁ {x} ⊆₁ (px₁ ∷ u₁) u uls dsj (¬hz ∷ hf) with
  hf-still ys [] [ (x , (cmdReadNames x s) , (cmdWriteNames x s)) ] _ ∀₁ u₁ uls₂ dsj₁ hf
  where dsj₁ : Disjoint ys (x ∷ map proj₁ _)
        dsj₁ = λ x₁ → dsj (there (proj₁ x₁) ,
               tail (λ v≡x → lookup px₁ (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
        uls₂ : Unique (x ∷ map proj₁ _)
        uls₂ = g₂ (map proj₁ _) (λ x₁ → dsj (here refl , x₁)) ∷ uls
        ∀₁ : ∀ f₁ → f₁ ∈ buildReadNames (run x s) ys → run x s f₁ ≡ s f₁
        ∀₁ = lemma3 (subst (λ x₁ → Disjoint x₁ (buildReadNames (run x s) ys))
                    (cmdWrote∷-≡ (x , (cmdReadNames x s) , (cmdWriteNames x s)) _)
                    (hf=>disjoint-∷ʳ ys (g₅ x ys px₁) (λ x₁ → ⊆₁ (there x₁))
                                     u hf))
... | hf₂ = hf-∷ʳ-r ys b₁ u hf₂
hf-drop-mid (x₁ ∷ xs) ys b₁ {x} ⊆₁ (px₁ ∷ u₁) u uls dsj (¬hz ∷ hf)
  = (¬hz-∷ʳ-r u ¬hz) ∷ (hf-drop-mid xs ys b₁ (λ x₃ → ⊆₁ (there x₃)) u₁ u uls₂ dsj₁ hf)
    where dsj₁ : Disjoint (xs ++ x ∷ ys) (x₁ ∷ map proj₁ _)
          dsj₁ = λ x₃ → dsj (there (proj₁ x₃) ,
                 tail (λ v≡x₁ → lookup px₁ (proj₁ x₃) (sym v≡x₁)) (proj₂ x₃))
          uls₂ : Unique (x₁ ∷ map proj₁ _)
          uls₂ = g₂ (map proj₁ _) (λ x₃ → dsj (here refl , x₃)) ∷ uls

∉=>¬before : ∀ {x : Cmd} {x₁} zs → x ∉ zs → ¬ (x before x₁ ∈ (zs ∷ʳ x))
{- need to prove ys is empty. then x₁ cannot be in empty list -}
∉=>¬before {x} [] x∉zs ([] , ys , ≡₁ , x₁∈ys) with ++-identityˡ (x ∷ [])
... | a with ∷-injectiveʳ ≡₁
... | refl = contradiction x₁∈ys (λ ())
∉=>¬before {x} [] x∉zs (x₂ ∷ xs , ys , ≡₁ , x₁∈ys) with ++-identityˡ (x ∷ [])
... | _ with ∷-injectiveʳ ≡₁
... | ≡₂ = contradiction (subst (λ x₃ → _ ∈ x₃) (sym ≡₂) (∈-++⁺ʳ xs (there x₁∈ys)))
                         (λ ())
∉=>¬before (x₂ ∷ zs) x∉zs ([] , ys , ≡₁ , x₁∈ys)
  = contradiction (here (sym (∷-injectiveˡ ≡₁))) x∉zs
∉=>¬before (x₂ ∷ zs) x∉zs (x₃ ∷ xs , ys , ≡₁ , x₁∈ys) with
  ∉=>¬before zs λ x₄ → x∉zs (there x₄)
... | ¬bf₁ = ¬bf₁ (xs , ys , ∷-injectiveʳ ≡₁ , x₁∈ys)

hf=>disjoint : ∀ s x xs ys {ls} → x ∈ map proj₁ ls → HazardFree s xs ys ls →
             Disjoint (filesRead ls) (buildWriteNames s xs)
hf=>disjoint s x [] ys x∈ hf = λ ()
hf=>disjoint s x (x₁ ∷ xs) ys {ls} x∈ (¬hz ∷ hf) with
  hf=>disjoint (run x₁ s) x xs ys (there x∈) hf
... | dsj = g₁
  where g₁ : Disjoint (filesRead ls) (buildWriteNames s (x₁ ∷ xs))
        g₁ (∈₁ , ∈₂) with ∈-++⁻ (cmdWriteNames x₁ s) ∈₂
        ... | inj₁ ∈cmd = ¬hz (ReadWrite ∈cmd ∈₁)
        ... | inj₂ ∈build = dsj (∈-++⁺ʳ _ ∈₁ , ∈build)

hf=>disjoint-∷ : ∀ s x xs ys {ls} → HazardFree s (x ∷ xs) ys ls →
               Disjoint (cmdReadNames x s) (buildWriteNames (run x s) xs)
hf=>disjoint-∷ s x [] ys hf = λ ()
hf=>disjoint-∷ s x xs ys (_ ∷ hf) p with hf=>disjoint (run x s) x xs ys (here refl) hf
... | dsj = dsj (∈-++⁺ˡ (proj₁ p) , (proj₂ p))

hf=>disjointWW3 : ∀ s x₁ zs x ls → x ∈ map proj₁ ls → x₁ ∈ zs → x ∉ zs →
                ¬ Hazard s x₁ (zs ∷ʳ x) ls →
                Disjoint (filesWrote ls) (cmdWriteNames x₁ s)
hf=>disjointWW3 s x₁ zs x ls x∈ls x₁∈zs x∉zs ¬hz x₄
  = ¬hz (WriteWrite (proj₂ x₄) (proj₁ x₄))

hf=>disjointWW2 : ∀ s ls ys zs x → ys ⊆ zs → x ∉ zs → x ∈ map proj₁ ls →
                HazardFree s ys (zs ∷ʳ x) ls →
                Disjoint (filesWrote ls) (buildWriteNames s ys)
hf=>disjointWW2 s ls [] zs x ys⊆zs x∉zs x∈ls hf = λ ()
hf=>disjointWW2 s ls (x₁ ∷ ys) zs x ys⊆zs x∉zs x∈ls (x₂ ∷ hf) with
  hf=>disjointWW2 (run x₁ s) (save s x₁ ls) ys zs x (λ x₃ → ys⊆zs (there x₃)) x∉zs
                  (there x∈ls) hf
... | dsj = g₁
  where g₁ : Disjoint (filesWrote ls) (buildWriteNames s (x₁ ∷ ys))
        g₁ (∈₁ , ∈₂) with ∈-++⁻ (cmdWriteNames x₁ s) ∈₂
        ... | inj₁ ∈cmd
          = hf=>disjointWW3 s x₁ zs x ls x∈ls (ys⊆zs (here refl)) x∉zs x₂ (∈₁ , ∈cmd)
        ... | inj₂ ∈build = dsj (∈-++⁺ʳ _ ∈₁ , ∈build)

hf=>disjointWW1 : ∀ s x ys zs ls → ys ⊆ zs → x ∉ zs →
                HazardFree s (x ∷ ys) (zs ∷ʳ x) ls →
                Disjoint (cmdWriteNames x s) (buildWriteNames (run x s) ys)
hf=>disjointWW1 s x ys zs ls ys⊆zs x∉zs (x₁ ∷ hf) with
  hf=>disjointWW2 (run _ s) (save s x ls) ys zs x ys⊆zs x∉zs (here refl) hf
... | dsj = λ x₂ → dsj (∈-++⁺ˡ (proj₁ x₂) , (proj₂ x₂))

hf=>disjointWW : ∀ s x xs ys zs ls → ys ⊆ zs → x ∉ zs →
               HazardFree s (xs ++ x ∷ ys) (zs ∷ʳ x) ls →
               Disjoint (cmdWriteNames x (script xs s))
                        (buildWriteNames (run x (script xs s)) ys)
hf=>disjointWW s x [] ys zs ls ys⊆zs x∉zs hf
  = hf=>disjointWW1 s x ys zs ls ys⊆zs x∉zs hf
hf=>disjointWW s x (x₁ ∷ xs) ys zs ls ys⊆zs x∉zs (x₂ ∷ hf)
  = hf=>disjointWW (run x₁ s) x xs ys zs _ ys⊆zs x∉zs hf

hf=>disjointRW3 : ∀ s x₁ zs x ls → x ∈ map proj₁ ls → x₁ ∈ zs → x ∉ zs →
                ¬ Hazard s x₁ (zs ∷ʳ x) ls →
                Disjoint (filesRead ls) (cmdWriteNames x₁ s)
hf=>disjointRW3 s x₁ zs x ls x∈ls x₁∈zs x∉zs ¬hz x₄
  = ¬hz (ReadWrite (proj₂ x₄) (proj₁ x₄))

hf=>disjointRW2 : ∀ s ls ys zs x → ys ⊆ zs → x ∉ zs → x ∈ map proj₁ ls →
                HazardFree s ys (zs ∷ʳ x) ls →
                Disjoint (filesRead ls) (buildWriteNames s ys)
hf=>disjointRW2 s ls [] zs x ys⊆zs x∉zs x∈ls hf = λ ()
hf=>disjointRW2 s ls (x₁ ∷ ys) zs x ys⊆zs x∉zs x∈ls (x₂ ∷ hf) with
  hf=>disjointRW2 (run x₁ s) (save s x₁ ls) ys zs x (λ x₃ → ys⊆zs (there x₃)) x∉zs
                  (there x∈ls) hf
... | dsj = g₁
  where g₁ : Disjoint (filesRead ls) (buildWriteNames s (x₁ ∷ ys))
        g₁ (∈₁ , ∈₂) with ∈-++⁻ (cmdWriteNames x₁ s) ∈₂
        ... | inj₁ ∈cmd
          = hf=>disjointRW3 s x₁ zs x ls x∈ls (ys⊆zs (here refl)) x∉zs x₂ (∈₁ , ∈cmd)
        ... | inj₂ ∈build = dsj (∈-++⁺ʳ _ ∈₁ , ∈build)

hf=>disjointRW1 : ∀ s x ys zs ls → ys ⊆ zs → x ∉ zs →
                HazardFree s (x ∷ ys) (zs ∷ʳ x) ls →
                Disjoint (cmdReadNames x s) (buildWriteNames (run x s) ys)
hf=>disjointRW1 s x ys zs ls ys⊆zs x∉zs (x₁ ∷ hf) with
  hf=>disjointRW2 (run _ s) (save s x ls) ys zs x ys⊆zs x∉zs (here refl) hf
... | dsj = λ x₂ → dsj (∈-++⁺ˡ (proj₁ x₂) , (proj₂ x₂))

hf=>disjointRW : ∀ s x xs ys zs ls → ys ⊆ zs → x ∉ zs →
               HazardFree s (xs ++ x ∷ ys) (zs ∷ʳ x) ls →
               Disjoint (cmdReadNames x (script xs s))
                        (buildWriteNames (run x (script xs s)) ys)
hf=>disjointRW s x [] ys zs ls ys⊆zs x∉zs hf
  = hf=>disjointRW1 s x ys zs ls ys⊆zs x∉zs hf
hf=>disjointRW s x (x₁ ∷ xs) ys zs ls ys⊆zs x∉zs (x₂ ∷ hf)
  = hf=>disjointRW (run x₁ s) x xs ys zs _ ys⊆zs x∉zs hf

hf=>disjointWR3 : ∀ s x₁ zs x ls → x ∈ map proj₁ ls → x₁ ∈ zs → x ∉ zs →
                ¬ Hazard s x₁ (zs ∷ʳ x) ls →
                Disjoint (cmdWrote ls x) (cmdReadNames x₁ s)
hf=>disjointWR3 s x₁ zs x ls x∈ls x₁∈zs x∉zs ¬hz x₄
  = ¬hz (Speculative x x₁ bf (∈-++⁺ˡ x₁∈zs) (∉=>¬before zs x∉zs)
                     (∈-cmdRead∷l (x₁ , (cmdReadNames x₁ s) , _) ls (proj₂ x₄))
                     (∈-cmdWrote∷ (x₁ , _ , _) x ls (proj₁ x₄)
                                  λ x₂ → x∉zs (subst (λ x₃ → x₃ ∈ zs) x₂ x₁∈zs)))
  where bf : x₁ before x ∈ (x₁ ∷ cmdsRun ls)
        bf = [] , cmdsRun ls , refl , x∈ls

hf=>disjointWR2 : ∀ s ls ys zs x → ys ⊆ zs → x ∉ zs → x ∈ map proj₁ ls →
                HazardFree s ys (zs ∷ʳ x) ls →
                Disjoint (cmdWrote ls x) (buildReadNames s ys)
hf=>disjointWR2 s ls [] zs x ys⊆zs x∉zs x∈ls hf = λ ()
hf=>disjointWR2 s ls (x₁ ∷ ys) zs x ys⊆zs x∉zs x∈ls (x₂ ∷ hf) with
  hf=>disjointWR2 (run x₁ s) (save s x₁ ls) ys zs x (λ x₃ → ys⊆zs (there x₃)) x∉zs
                  (there x∈ls) hf
... | dsj = g₁
  where g₁ : Disjoint (cmdWrote ls x) (buildReadNames s (x₁ ∷ ys))
        g₁ (∈₁ , ∈₂) with ∈-++⁻ (cmdReadNames x₁ s) ∈₂
        ... | inj₁ ∈cmd
          = hf=>disjointWR3 s x₁ zs x ls x∈ls (ys⊆zs (here refl)) x∉zs x₂ (∈₁ , ∈cmd)
        ... | inj₂ ∈build
          = dsj (∈-cmdWrote∷ (x₁ , _ , _) x ls ∈₁
                             (λ x₃ → x∉zs (subst (λ x₄ → x₄ ∈ zs) x₃
                                                  (ys⊆zs (here refl)))) , ∈build)

hf=>disjointWR1 : ∀ s x ys zs ls → ys ⊆ zs → x ∉ zs →
                HazardFree s (x ∷ ys) (zs ∷ʳ x) ls →
                Disjoint (cmdWriteNames x s) (buildReadNames (run x s) ys)
hf=>disjointWR1 s x ys zs ls ys⊆zs x∉zs (x₁ ∷ hf) with
  hf=>disjointWR2 (run _ s) (save s x ls) ys zs x ys⊆zs x∉zs (here refl) hf
... | dsj = λ x₂ → dsj (∈-cmdWrote∷l (x , _ , (cmdWriteNames x s)) ls (proj₁ x₂) ,
                        proj₂ x₂)

hf=>disjointWR : ∀ s x xs ys zs ls → ys ⊆ zs → x ∉ zs →
               HazardFree s (xs ++ x ∷ ys) (zs ∷ʳ x) ls →
               Disjoint (cmdWriteNames x (script xs s))
                        (buildReadNames (run x (script xs s)) ys)
hf=>disjointWR s x [] ys zs ls ys⊆zs x∉zs hf
  = hf=>disjointWR1 s x ys zs ls ys⊆zs x∉zs hf
hf=>disjointWR s x (x₁ ∷ xs) ys zs ls ys⊆zs x∉zs (x₂ ∷ hf)
  = hf=>disjointWR (run x₁ s) x xs ys zs _ ys⊆zs x∉zs hf


intersection? : (xs ys : List FileName) → Dec (∃[ v ](v ∈ xs × v ∈ ys))
intersection? [] ys = false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
intersection? (x ∷ xs) ys with x ∈? ys
... | yes x∈ys = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : ∃[ v ](v ∈ x ∷ xs × v ∈ ys)
        g₁ = x , here refl , x∈ys
... | no x∉ys with intersection? xs ys
... | yes (v , v∈xs , v∈ys)
  = true Relation.Nullary.because Relation.Nullary.ofʸ (v , there v∈xs , v∈ys)
... | no ¬p = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (∃[ v ](v ∈ x ∷ xs × v ∈ ys))
        g₁ (v , v∈x∷xs , v∈ys) with v ≟ x
        ... | yes v≡x = contradiction (subst (λ x₁ → x₁ ∈ ys) v≡x v∈ys) x∉ys
        ... | no ¬v≡x = ¬p (v , (tail ¬v≡x v∈x∷xs) , v∈ys)

before? : ∀ (x₁ : Cmd) x b → Dec (x₁ before x ∈ b)
before? x₁ x [] = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (x₁ before x ∈ [])
        g₁ (xs , ys , ≡₁ , x∈ys)
          = contradiction (subst (λ x₂ → x ∈ x₂) (sym ≡₁) (∈-++⁺ʳ xs (there x∈ys)))
                          λ ()
before? x₁ x (x₂ ∷ b) with x₁ ≟ x₂
... | yes x₁≡x₂ with x ∈? b
... | yes x∈b = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : x₁ before x ∈ (x₂ ∷ b)
        g₁ = [] , b , cong (_∷ b) (sym x₁≡x₂) , x∈b
... | no x∉b = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (x₁ before x ∈ (x₂ ∷ b))
        g₁ ([] , ys , x₂∷b≡x₁∷ys , x∈ys)
          = contradiction (subst (λ x₃ → x ∈ x₃) (sym (∷-injectiveʳ x₂∷b≡x₁∷ys)) x∈ys)
                          x∉b
        g₁ (x₃ ∷ xs , ys , x₂∷b≡xs++x₁∷ys , x∈ys)
          = contradiction (subst (λ x₄ → x ∈ x₄) (sym (∷-injectiveʳ x₂∷b≡xs++x₁∷ys))
                                 (∈-++⁺ʳ xs (there x∈ys))) x∉b
before? x₁ x (x₂ ∷ b) | no ¬x₁≡x₂ with before? x₁ x b
... | yes (xs , ys , ≡₁ , x∈ys)
  = true Relation.Nullary.because Relation.Nullary.ofʸ
         (x₂ ∷ xs , ys , cong (x₂ ∷_) ≡₁ , x∈ys)
... | no ¬bf = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (x₁ before x ∈ (x₂ ∷ b))
        g₁ ([] , ys , ≡₁ , x∈ys) = contradiction (sym (∷-injectiveˡ ≡₁)) ¬x₁≡x₂
        g₁ (x₃ ∷ xs , ys , ≡₁ , x∈ys) = ¬bf (xs , ys , ∷-injectiveʳ ≡₁ , x∈ys)

-- does there exist a command in ls that writes to these files 
-- and is not before x in b?
speculativeHazard-x? : ∀ x b₂ ls ls₁ rs →
                     Dec (∃[ x₁ ](∃[ v ](x₁ ∈ ls × ¬ (x₁ before x ∈ b₂) ×
                                        v ∈ rs × v ∈ cmdWrote ls₁ x₁)))
speculativeHazard-x? x b₂ [] ls₁ rs
  = false Relation.Nullary.because Relation.Nullary.ofⁿ (λ ())
speculativeHazard-x? x b₂ (x₁ ∷ ls) ls₁ rs with intersection? rs (cmdWrote ls₁ x₁)
... | yes (v , v∈rs , v∈ws) with before? x₁ x b₂
... | no ¬bf = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : ∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs ×
                           v ∈ cmdWrote ls₁ x₂))
        g₁ = x₁ , v , here refl , ¬bf , v∈rs , v∈ws
... | yes bf with speculativeHazard-x? x b₂ ls ls₁ rs
... | yes (x₂ , v₂ , x₂∈ , ¬bf , a , a₁) = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : ∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs ×
                           v ∈ cmdWrote ls₁ x₂))
        g₁ = x₂ , v₂ , there x₂∈ , ¬bf , a , a₁
... | no ¬p = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs ×
                              v ∈ cmdWrote ls₁ x₂)))
        g₁ (x₂ , v , x₂∈ , ¬bf , v∈rs , v∈ws) with x₂ ≟ x₁
        ... | yes x₂≡x₁
          = contradiction (subst (λ x₃ → x₃ before x ∈ b₂) (sym x₂≡x₁) bf) ¬bf
        ... | no ¬x₂≡x₁ = ¬p (x₂ , v , tail ¬x₂≡x₁ x₂∈ , ¬bf , v∈rs , v∈ws)
speculativeHazard-x? x b₂ (x₁ ∷ ls) ls₁ rs | no p₁ with speculativeHazard-x? x b₂ ls ls₁ rs
... | yes (x₂ , v₂ , x₂∈ , ¬bf , a , a₁) = true Relation.Nullary.because Relation.Nullary.ofʸ g₁
  where g₁ : ∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs ×
                    v ∈ cmdWrote ls₁ x₂))
        g₁ = x₂ , v₂ , there x₂∈ , ¬bf , a , a₁
... | no ¬p = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ (∃[ x₂ ](∃[ v ](x₂ ∈ (x₁ ∷ ls) × ¬ (x₂ before x ∈ b₂) × v ∈ rs ×
                              v ∈ cmdWrote ls₁ x₂)))
        g₁ (x₂ , v , x₂∈ , ¬bf , v∈rs , v∈ws) with x₂ ≟ x₁
        ... | yes x₂≡x₁
          = p₁ (v , (v∈rs , subst (λ x₃ → v ∈ cmdWrote ls₁ x₃) x₂≡x₁ v∈ws))
        ... | no ¬x₂≡x₁ = ¬p (x₂ , v , tail ¬x₂≡x₁ x₂∈ , ¬bf , v∈rs , v∈ws)

¬speculative? : ∀ b₂ ls →
              Dec (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ (map proj₁ ls)) × x₂ ∈ b₂ ×
                                        ¬ (x₁ before x₂ ∈ b₂) × v ∈ cmdRead ls x₂ ×
                                        v ∈ cmdWrote ls x₁))))
¬speculative? b₂ ls = g₁ b₂ (map proj₁ ls) ls
  where g₁ : ∀ b₂ ls₁ ls₂ →
           Dec (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ ls₁) × x₂ ∈ b₂ ×
                                      ¬ (x₁ before x₂ ∈ b₂) × v ∈ cmdRead ls₂ x₂ ×
                                      v ∈ cmdWrote ls₂ x₁))))
        g₁ b₂ [] ls₂ = false Relation.Nullary.because Relation.Nullary.ofⁿ g₆
          where g₆ : ¬ (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ []) × x₂ ∈ b₂ ×
                                              ¬ (x₁ before x₂ ∈ b₂) ×
                                              v ∈ cmdRead ls₂ x₂ ×
                                              v ∈ cmdWrote ls₂ x₁))))
                g₆ (_ , _ , _ , (xs , ys , ≡₁ , x₁∈ys) , rest)
                  = contradiction (subst (λ x → _ ∈ x) (sym ≡₁)
                                         (∈-++⁺ʳ xs (there x₁∈ys)))
                                  (λ ())
        g₁ b₂ (x ∷ ls₁) ls₂ with x ∈? b₂
        ... | yes x∈b₂ with speculativeHazard-x? x b₂ ls₁ ls₂ (cmdRead ls₂ x)
        ... | yes (x₁ , v , x₁∈ls , ¬bf , v∈rs , v∈ws)
          = true Relation.Nullary.because Relation.Nullary.ofʸ
            (x₁ , x , v , ([] , ls₁ , refl , x₁∈ls) , x∈b₂ , ¬bf ,  v∈rs , v∈ws)
        ... | no ¬p with g₁ b₂ ls₁ ls₂
        ... | yes (x₁ , x₂ , v , (xs , ys , ≡₁ , ∈₁) , rest)
          = true Relation.Nullary.because Relation.Nullary.ofʸ
            (x₁ , x₂ , v , (x ∷ xs , ys , cong (x ∷_) ≡₁ , ∈₁) , rest)
        ... | no ¬sh = false Relation.Nullary.because Relation.Nullary.ofⁿ g₆
          where g₆ : ¬ (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ (x ∷ ls₁)) × x₂ ∈ b₂ ×
                                             ¬ (x₁ before x₂ ∈ b₂) ×
                                             v ∈ cmdRead ls₂ x₂ ×
                                             v ∈ cmdWrote ls₂ x₁))))
                g₆ (x₁ , x₂ , v , ([] , ys , ≡₁ , ∈₁) , x₂∈b₂ , ¬bf , v∈rs , v∈ws)
                  = ¬p (x₁ , v , subst (λ x₃ → x₁ ∈ x₃) (sym (∷-injectiveʳ ≡₁))
                                       ∈₁ , subst (λ x₃ → ¬ (x₁ before x₃ ∈ b₂))
                                                  (sym (∷-injectiveˡ ≡₁)) ¬bf
                       , subst (λ x₃ → v ∈ cmdRead ls₂ x₃)
                               (sym (∷-injectiveˡ ≡₁)) v∈rs , v∈ws)
                g₆ (x₁ , x₂ , v , (x₃ ∷ xs , ys , ≡₁ , ∈₁) , rest)
                  = ¬sh (x₁ , x₂ , v , (xs , ys , (∷-injectiveʳ ≡₁) , ∈₁) , rest)
        g₁ b₂ (x ∷ ls₁) ls₂ | no x∉b₂ with g₁ b₂ ls₁ ls₂
        ... | yes (x₁ , x₂ , v , (xs , ys , ≡₁ , ∈₁) , rest)
          = true Relation.Nullary.because Relation.Nullary.ofʸ
            (x₁ , x₂ , v , (x ∷ xs , ys , cong (x ∷_) ≡₁ , ∈₁) , rest)
        ... | no ¬sh = false Relation.Nullary.because Relation.Nullary.ofⁿ g₆
          where g₆ : ¬ (∃[ x₁ ](∃[ x₂ ](∃[ v ]((x₂ before x₁ ∈ (x ∷ ls₁)) × x₂ ∈ b₂ ×
                                             ¬ (x₁ before x₂ ∈ b₂) × v ∈ cmdRead ls₂ x₂ ×
                                             v ∈ cmdWrote ls₂ x₁))))
                g₆ (x₁ , x₂ , v , ([] , ys , ≡₁ , ∈₁) , x₂∈b₂ , ¬bf , v∈rs , v∈ws)
                  = contradiction (subst (λ x₃ → x₃ ∈ b₂) (sym (∷-injectiveˡ ≡₁))
                                         x₂∈b₂)
                                  x∉b₂
                g₆ (x₁ , x₂ , v , (x₃ ∷ xs , ys , ≡₁ , ∈₁) , rest)
                  = ¬sh (x₁ , x₂ , v , (xs , ys , (∷-injectiveʳ ≡₁) , ∈₁) , rest)

hazard? : ∀ s x b₂ ls → Dec (Hazard s x b₂ ls)
hazard? s x b₂ ls with intersection? (cmdWriteNames x s) (filesRead ls)
... | yes (v , ∈₁ , ∈₂)
  = true Relation.Nullary.because Relation.Nullary.ofʸ (ReadWrite ∈₁ ∈₂)
... | no ¬x₁ with intersection? (cmdWriteNames x s) (filesWrote ls)
... | yes (v , ∈₁ , ∈₂)
  = true Relation.Nullary.because Relation.Nullary.ofʸ (WriteWrite ∈₁ ∈₂)
... | no ¬x₂ with ¬speculative? b₂ (save s x ls)
... | yes (x₁ , x₂ , v , bf , x₂∈b₂ , ¬bf , v∈₁ , v∈₂)
  = true Relation.Nullary.because Relation.Nullary.ofʸ
         (Speculative x₁ x₂ bf x₂∈b₂ ¬bf v∈₁ v∈₂)
... | no ¬sh = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ Hazard s x b₂ ls
        g₁ (ReadWrite x x₁) = ¬x₁ (_ , (x , x₁))
        g₁ (WriteWrite x x₁) = ¬x₂ (_ , (x , x₁))
        g₁ (Speculative x₁ x₂ y x₃ x₄ x₅ x₆)
          = ¬sh (x₁ , x₂ , _ , y , x₃ , x₄ , x₅ , x₆)

hazardfree? : ∀ s b₁ b₂ ls → Dec (HazardFree s b₁ b₂ ls)
hazardfree? s [] b₂ ls = true Relation.Nullary.because Relation.Nullary.ofʸ []
hazardfree? s (x ∷ b₁) b₂ ls with hazard? s x b₂ ls
... | yes hz = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ HazardFree s (x ∷ b₁) b₂ ls
        g₁ (¬hz ∷ hf) = ¬hz hz
... | no ¬hz with hazardfree? (run x s) b₁ b₂ (save s x ls)
... | yes hf = true Relation.Nullary.because Relation.Nullary.ofʸ (¬hz ∷ hf)
... | no ¬hf = false Relation.Nullary.because Relation.Nullary.ofⁿ g₁
  where g₁ : ¬ HazardFree s (x ∷ b₁) b₂ ls
        g₁ (_ ∷ hf) = ¬hf hf
