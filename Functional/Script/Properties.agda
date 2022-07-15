open import Functional.State using (Oracle ; FileSystem ; Cmd ; extend)

module Functional.Script.Properties (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle)
  using (run ; cmdWriteNames ; cmdReadNames ; cmdWrites)
open import Functional.State.Properties (oracle)
  using (run-cong-All-sym ; run-cong₂-File ; run-unchanged-File ; run-cong-File ;
         run-unchanged-All ; run-cong) 
open import Functional.Build (oracle)
  using (Build ; DisjointBuild ; _∷_ ; [] ; PreCond ; UniqueEvidence)
open import Functional.Script.Exec (oracle)
  using (script ; buildReadNames ; buildWriteNames)
open import Functional.Script.Hazard (oracle)
  using (HazardFree ; FileInfo ; _∷_ ; WriteWrite)
open import Functional.Script.Hazard.Properties (oracle)
  using (hf=>disjoint-∷ ; hf-drop-mid ; hf=>disjointWW ; hf=>disjointRW ; hf=>disjointWR)
open import Data.List using (List ; _∷ʳ_ ; _∷_ ; _++_ ; [] ; map ; foldr ; reverse ; length)
open import Data.List.Properties using (++-identityʳ ; unfold-reverse ; reverse-involutive)
open import Data.String using (String)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
  using (subst ; subst₂ ; sym ; trans ; cong ; cong₂ ; cong-app ; decSetoid)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Product using (proj₂ ; proj₁ ; _,_)
open import Data.String.Properties using (_≟_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈?_ ; _∉_ ; _∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-∃++ ; ∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_ ; ↭-trans ; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++↭ʳ++ ; ∈-resp-↭ ; drop-mid ; ↭-length)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.All as All using (All ; lookup ; _∷_) 
open import Data.List.Relation.Unary.All.Properties as AllP using (++⁻)
open import Data.List.Relation.Unary.Any as Any using (here ; there)
open import Data.List.Relation.Unary.Any.Properties using (reverse⁺ ; reverse⁻)
open import Data.List.Relation.Unary.Unique.Propositional
  using (Unique ; _∷_ ; [] ; head ; tail)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (++⁺)
open import Function using (_∘_)
open import Data.Empty using (⊥)

-- h₄ and h₅
g₁ : (s s₁ : FileSystem) (x : Cmd) → All (λ f₁ → s f₁ ≡ s₁ f₁) (cmdReadNames x s₁) →
   proj₁ (oracle x) s ≡ proj₁ (oracle x) s₁
g₁ s s₁ x all₁ = sym (proj₂ (oracle x) s₁ s λ f₁ x₁ → sym (lookup all₁ x₁))

--- script properties ---

script-≡₁ : ∀ {s} → (x : Cmd) (b : Build) → run x (script b s) ≡ script (b ∷ʳ x) s
script-≡₁ x [] = refl
script-≡₁ x (x₁ ∷ b) = script-≡₁ x b

-- exec-∷≡
script-≡₂ : (f₁ : String) (s s₁ : FileSystem) (b : Build) →
          All (λ f₂ → s f₂ ≡ s₁ f₂) (buildReadNames s₁ b) →
          s f₁ ≡ s₁ f₁ → script b s f₁ ≡ script b s₁ f₁
script-≡₂ f₁ s s₁ [] all₁ ≡₁ = ≡₁
script-≡₂ f₁ s s₁ (x₁ ∷ b) all₁ ≡₁ with ++⁻ (cmdReadNames x₁ s₁) all₁ 
... | all₂ , all₃ = script-≡₂ f₁ (run x₁ s) (run x₁ s₁) b
                     (run-cong-All-sym (buildReadNames (run x₁ s₁) b) x₁ all₂ all₃)
                                       (run-cong₂-File (g₁ s s₁ x₁ all₂) ≡₁)

-- exec-≡sys
script-≡₃ : ∀ {f₁} (s : FileSystem) (xs : Build) → f₁ ∉ buildWriteNames s xs →
          script xs s f₁ ≡ s f₁
script-≡₃ s [] f₁∉ = refl
script-≡₃ {f₁} s (x ∷ xs) f₁∉
  = trans (script-≡₃ (run x s) xs (λ x₁ → f₁∉ (∈-++⁺ʳ (cmdWriteNames x s) x₁)))
          (sym (run-unchanged-File f₁ (proj₂ (proj₁ (oracle x) s))
                                   λ x₁ → f₁∉ (∈-++⁺ˡ x₁)))

-- if f₁ is not in the writes if ys then
-- f₁ is the same in the system before and after ys executes
-- exec-≡f₁
script-≡₄ : (s : FileSystem) (f₁ : String) (xs ys : Build) →
          f₁ ∉ buildWriteNames (script xs s) ys →
          script xs s f₁ ≡ script (xs ++ ys) s f₁
script-≡₄ s f₁ [] ys f₁∉ = sym (script-≡₃ s ys f₁∉)
script-≡₄ s f₁ (x ∷ xs) ys f₁∉ = script-≡₄ (run x s) f₁ xs ys f₁∉

script-≡₅ : ∀ {s} xs ys → script (xs ++ ys) s ≡ script ys (script xs s)
script-≡₅ [] ys = refl
script-≡₅ (x ∷ xs) ys = script-≡₅ xs ys


writes-≡ : (s s₁ : FileSystem) (ys : Build) →
         All (λ f₁ → s f₁ ≡ s₁ f₁) (buildReadNames s₁ ys) →
         buildWriteNames s ys ≡ buildWriteNames s₁ ys
writes-≡ s s₁ [] all₁ = refl
writes-≡ s s₁ (x₁ ∷ ys) all₁ with ++⁻ (cmdReadNames x₁ s₁) all₁
... | all₂ , all₃
  = cong₂ _++_ (cong ((map proj₁) ∘ proj₂) (g₁ s s₁ x₁ all₂))
          (writes-≡ (run x₁ s) (run x₁ s₁) ys
                    (run-cong-All-sym (buildReadNames (run x₁ s₁) ys) x₁ all₂ all₃))

disjointBuild-≡ : ∀ s₁ s₂ b₁ → (∀ f₁ → s₂ f₁ ≡ s₁ f₁) → DisjointBuild s₁ b₁ →
                DisjointBuild s₂ b₁
disjointBuild-≡ s₁ s₂ .[] ∀₁ [] = []
disjointBuild-≡ s₁ s₂ (x ∷ b) ∀₁ (dsj ∷ dsb)
  = (λ x₂ → dsj (v∈reads (proj₁ x₂) , v∈writes (proj₂ x₂))) ∷
    (disjointBuild-≡ (run x s₁) (run x s₂) b (run-cong x ∀₁) dsb)
  where ≡₁ : proj₁ (oracle x) s₂ ≡ proj₁ (oracle x) s₁
        ≡₁ = proj₂ (oracle x) s₂ s₁ λ f₁ x₁ → ∀₁ f₁
        v∈reads : ∀ {v} → v ∈ cmdReadNames x s₂ → v ∈ cmdReadNames x s₁
        v∈reads v∈ = subst (λ x₁ → _ ∈ x₁) (cong (map proj₁ ∘ proj₁) ≡₁) v∈
        v∈writes : ∀ {v} → v ∈ cmdWriteNames x s₂ → v ∈ cmdWriteNames x s₁
        v∈writes v∈ = subst (λ x₁ → _ ∈ x₁) (cong (map proj₁ ∘ proj₂) ≡₁) v∈

-- idempotence proof --

idempotent-lemma : ∀ {ls} {b₁} s₁ s₂ b → DisjointBuild s₁ b → HazardFree s₁ b b₁ ls →
                 (∀ f₁ → f₁ ∉ buildWriteNames s₁ b → s₁ f₁ ≡ s₂ f₁) →
                 (∀ f₁ → script b s₁ f₁ ≡ script b s₂ f₁)
idempotent-lemma s₁ s₂ [] _ _ ∀₁ f₁ = ∀₁ f₁ ∈₁
  where ∈₁ : f₁ ∉ buildWriteNames s₁ []
        ∈₁ ()
idempotent-lemma s₁ s₂ (x ∷ b) (dsj ∷ dsb) (¬hz ∷ hf) ∀₁
  = idempotent-lemma (run x s₁) (run x s₂) b dsb hf (λ f₁ x₁ → g₄ f₁ x₁)
  where g₂ : ∀ f₁ → f₁ ∉ cmdWriteNames x s₁ → f₁ ∉ buildWriteNames (run x s₁) b →
           f₁ ∈ buildWriteNames s₁ (x ∷ b) → ⊥
        g₂ f₁ f₁∉₁ f₁∉₂ f₁∈ with ∈-++⁻ (cmdWriteNames x s₁) f₁∈
        ... | inj₁ ∈₁ = contradiction ∈₁ f₁∉₁
        ... | inj₂ ∈₂ = contradiction ∈₂ f₁∉₂
        g₃ : ∀ f₁ → f₁ ∈ cmdReadNames x s₁ → s₁ f₁ ≡ s₂ f₁
        g₃ f₁ f₁∈ with hf=>disjoint-∷ s₁ x b _ (¬hz ∷ hf)
        ... |  dsj₂ = ∀₁ f₁ λ x₁ → g₂ f₁ (λ x₂ → dsj (f₁∈ , x₂))
                    (λ x₂ → dsj₂ (f₁∈ , x₂)) x₁
        
        g₄ : ∀ f₁ → f₁ ∉ buildWriteNames (run x s₁) b → run x s₁ f₁ ≡ run x s₂ f₁
        g₄ f₁ p with proj₂ (oracle x) s₁ s₂ (λ f₂ x₁ → g₃ f₂ x₁)
        ... | ≡₁ with f₁ ∈? cmdWriteNames x s₁
        ... | yes f₁∈ws = subst (λ x₁ → run x s₁ f₁ ≡ foldr extend s₂ x₁ f₁)
                                (cong proj₂ ≡₁)
                                (run-cong-File (proj₂ (proj₁ (oracle x) s₁)) f₁ f₁∈ws) 
        ... | no f₁∉ws = run-cong₂-File ≡₁ (∀₁ f₁ λ x₁ → g₂ f₁ f₁∉ws p x₁)

script-idempotent : ∀ s b {b₁} {ls} → DisjointBuild s b → HazardFree s b b₁ ls →
                  (∀ f₁ → script b s f₁ ≡ script b (script b s) f₁)
script-idempotent s b dsb hf
  = idempotent-lemma s (script b s) b dsb hf λ f₁ x → sym (script-≡₃ s b x)

-- reordering proof and helper lemmas --

all-drop-mid : ∀ (xs : Build) {ys} {x} {x₁} → All (λ y → ¬ x₁ ≡ y) (xs ++ x ∷ ys) →
             All (λ y → ¬ x₁ ≡ y) (xs ++ ys)
all-drop-mid [] all₁ = All.tail all₁
all-drop-mid (x₂ ∷ xs) all₁ = (All.head all₁) ∷ (all-drop-mid xs (All.tail all₁))

unique-drop-mid : ∀ (xs : Build) {ys} {x} → Unique (xs ++ x ∷ ys) → Unique (xs ++ ys)
unique-drop-mid [] (x₁ ∷ u) = u
unique-drop-mid (x₁ ∷ xs) u = (all-drop-mid xs (head u)) ∷ (unique-drop-mid xs (tail u))

unique→disjoint : ∀ {x₁ : Cmd} xs → All (λ y → ¬ x₁ ≡ y) xs → Disjoint xs (x₁ ∷ [])
unique→disjoint [] All.[] = λ ()
unique→disjoint (x ∷ xs) (¬x₁≡x ∷ all₁) x₂
  = unique→disjoint xs all₁ (Any.tail (λ v≡x → ¬x₁≡x (trans (g₂ (proj₂ x₂)) v≡x))
                                      (proj₁ x₂) , proj₂ x₂)
  where g₂ : ∀ {v} {x₁} → v ∈ x₁ ∷ [] → x₁ ≡ v
        g₂ (here px) = sym px

all-reverse : ∀ {x₁ : Cmd} xs → All (λ y → ¬ x₁ ≡ y) xs →
            All (λ y → ¬ x₁ ≡ y) (reverse xs)
all-reverse [] All.[] = All.[]
all-reverse (x ∷ xs) (px ∷ all₁)
  = subst (λ x₂ → All (λ y → ¬ _ ≡ y) x₂)
          (sym (unfold-reverse x xs)) (AllP.++⁺ (all-reverse xs all₁) (px ∷ All.[]))

unique-reverse : ∀ xs → Unique xs → Unique (reverse xs)
unique-reverse [] u = []
unique-reverse (x₁ ∷ xs) (px ∷ u) with
  ++⁺ (unique-reverse xs u) (All.[] ∷ [])
      (unique→disjoint (reverse xs) (all-reverse xs px))
... | u₁ = subst (λ ls → Unique ls) (sym (unfold-reverse x₁ xs)) u₁

↭-reverse : ∀ (xs : Build) → xs ↭ reverse xs
↭-reverse xs = subst (λ x → x ↭ reverse xs) (++-identityʳ xs) (++↭ʳ++ xs [])

lemma1 : ∀ {s} as bs xs x → Disjoint (cmdReadNames x (script as s))
                                      (buildWriteNames (script as s) bs) →
       (∀ f₁ → script (as ++ bs) s f₁ ≡ script xs s f₁) →
       proj₁ (oracle x) (script as s) ≡ proj₁ (oracle x) (script xs s)
lemma1 {s} as bs xs x dsj ∀₁
  = proj₂ (oracle x) (script as s) (script xs s)
          λ f₁ x₁ → trans (script-≡₄ s f₁ as bs (λ f₁∈writes → dsj (x₁ , f₁∈writes)))
                           (∀₁ f₁)

lemma2 : ∀ {s} {f₁} xs x → f₁ ∉ cmdWriteNames x s →
       All (λ f₁ → s f₁ ≡ run x s f₁) (buildReadNames (run x s) xs) →
       script (x ∷ xs) s f₁ ≡ script xs s f₁
lemma2 {s} xs x f₁∉ all₁
  = sym (script-≡₂ _ s (run x s) xs all₁ (run-unchanged-File _ (cmdWrites x s) f₁∉))

-- we can add back the command we removed.
add-back : ∀ {s} as bs xs x →
         Disjoint (cmdWriteNames x (script as s))
                  (buildWriteNames (run x (script as s)) bs) →
         Disjoint (cmdReadNames x (script as s))
                  (buildWriteNames (run x (script as s)) bs) →
         Disjoint (cmdWriteNames x (script as s))
                  (buildReadNames (run x (script as s)) bs) →
         (∀ f₁ → script (as ++ bs) s f₁ ≡ script xs s f₁) →
         (∀ f₁ → script (as ++ x ∷ bs) s f₁ ≡ script (xs ++ x ∷ []) s f₁)
add-back {s} as bs xs x dsj₀ dsj dsj₁ ∀₁ f₁ with
  run-unchanged-All (buildReadNames (run x (script as s)) bs) (cmdWrites x (script as s))
                    dsj₁
... | all₁ with writes-≡ (script as s) (run x (script as s)) bs all₁
... | ≡₁   with lemma1 as bs xs x (subst (λ x₁ → Disjoint _ x₁) (sym ≡₁) dsj) ∀₁
... | x≡   with f₁ ∈? cmdWriteNames x (script as s)
-- we know as ++ x ≡ xs ++ x. just show bs doesnt change what x wrote to.
... | yes f₁∈ = trans ≡₂ ≡₃
  where ≡₂ : script (as ++ x ∷ bs) s f₁ ≡ run x (script as s) f₁
        ≡₂ = trans (cong-app (script-≡₅ as (x ∷ bs)) f₁)
                   (script-≡₃ (run x (script as s)) bs λ x₁ → dsj₀ (f₁∈ , x₁))
        ≡₃ : run x (script as s) f₁ ≡ script (xs ++ x ∷ []) s f₁
        ≡₃ = trans (subst (λ x₁ → run x (script as s) _ ≡ foldr extend (script xs s) x₁ _)
                          (cong proj₂ x≡)
                          (run-cong-File (cmdWrites x (script as s)) _ f₁∈))
                   (sym (cong-app (script-≡₅ xs (x ∷ [])) f₁))
        
... | no f₁∉ with trans (cong-app (script-≡₅ as (x ∷ bs)) f₁)
                        (trans (lemma2 bs x f₁∉ all₁)
                               (sym (cong-app (script-≡₅ as bs) f₁)))
... | ≡₂ with trans (run-unchanged-File _ (cmdWrites x (script xs s))
                                          (subst (λ x₁ → _ ∉ x₁)
                                                 (cong (map proj₁ ∘ proj₂) x≡) f₁∉))
                    (cong-app (script-≡₁ x xs) f₁)
... | ≡₃ = trans ≡₂ (trans (∀₁ f₁) ≡₃)

-- the workhorse
reordered : ∀ {s} {ls} xs ys → length xs ≡ length ys → xs ↭ ys →
          UniqueEvidence xs ys (map proj₁ ls) → HazardFree s xs (reverse ys) ls →
          (∀ f₁ → script xs s f₁ ≡ script (reverse ys) s f₁)
reordered [] [] _ p _ hf f₁ = refl
reordered {s} {ls} xs (x ∷ ys) _ p (uxs , ux ∷ uys , uls , dsj) hf f₁ with
  ∈-∃++ (∈-resp-↭ (↭-sym p) (here refl))
... | (as , bs , ≡₁) with
  add-back as bs (reverse ys) x dsj₁ dsj₂ dsj₃
           (reordered (as ++ bs) ys (↭-length ↭₂) ↭₂ (uas++bs , uys , uls , dsj₀) hf₁)
  where ↭₂ : as ++ bs ↭ ys
        ↭₂ = drop-mid as [] (subst (λ x₁ → x₁ ↭ x ∷ ys) ≡₁ p)
        uas++bs : Unique (as ++ bs)
        uas++bs = unique-drop-mid as (subst (λ x₁ → Unique x₁) ≡₁ uxs)
        dsj₀ : Disjoint (as ++ bs) (map proj₁ ls)
        dsj₀ x₂ with ∈-++⁻ as (proj₁ x₂)
        ... | inj₁ _∈as = dsj (subst (λ x₁ → _ ∈ x₁)
                                     (sym ≡₁) (∈-++⁺ˡ _∈as) , (proj₂ x₂))
        ... | inj₂ _∈bs = dsj (subst (λ x₁ → _ ∈ x₁)
                                     (sym ≡₁) (∈-++⁺ʳ as (there _∈bs)) , (proj₂ x₂))
        ⊆₁ : as ++ x ∷ bs ⊆ reverse ys ++ x ∷ []
        ⊆₁ x₁∈as++x∷bs = subst (λ x₂ → _ ∈ x₂)
                               (unfold-reverse x ys)
                               (reverse⁺ (∈-resp-↭ p (subst (λ x₂ → _ ∈ x₂)
                                                             (sym ≡₁) x₁∈as++x∷bs)))
        hf₀ : HazardFree s (as ++ x ∷ bs) ((reverse ys) ++ x ∷ []) _
        hf₀ = subst₂ (λ x₂ x₃ → HazardFree s x₂ x₃ _) ≡₁ (unfold-reverse x ys) hf
        hf₁ : HazardFree s (as ++ bs) (reverse ys) _
        hf₁ = hf-drop-mid as bs (reverse ys) ⊆₁
                          (subst (λ x₁ → Unique x₁) ≡₁ uxs)
                          (subst (λ x₁ → Unique x₁)
                                 (unfold-reverse x ys)
                                 (unique-reverse (x ∷ ys) (ux ∷ uys)))
                          uls
                          (subst (λ x₁ → Disjoint x₁ _) ≡₁ dsj)
                          hf₀
        bs⊆reverse-ys : bs ⊆ reverse ys
        bs⊆reverse-ys x₃ = reverse⁺ (∈-resp-↭ ↭₂ (∈-++⁺ʳ as x₃))
        x∉reverse-ys : x ∉ reverse ys
        x∉reverse-ys x∈reverse-ys = lookup ux (reverse⁻ x∈reverse-ys) refl
        dsj₁ : Disjoint (cmdWriteNames x (script as _))
                        (buildWriteNames (run x (script as _)) bs)
        dsj₁ = hf=>disjointWW s x as bs (reverse ys) _  bs⊆reverse-ys x∉reverse-ys hf₀
        dsj₂ : Disjoint (cmdReadNames x (script as _))
                        (buildWriteNames (run x (script as _)) bs)
        dsj₂ = hf=>disjointRW s x as bs (reverse ys) _ bs⊆reverse-ys x∉reverse-ys hf₀
        dsj₃ : Disjoint (cmdWriteNames x (script as _))
                        (buildReadNames (run x (script as _)) bs)
        dsj₃ = hf=>disjointWR s x as bs (reverse ys) _ bs⊆reverse-ys x∉reverse-ys hf₀
... | ∀₂ = subst₂ (λ x₂ x₃ → script x₂ _ f₁ ≡ script x₃ _ f₁)
                  (sym ≡₁) (sym (unfold-reverse x ys)) (∀₂ f₁)

reordered-≡ : ∀ s br bc → PreCond s br bc → HazardFree s br bc [] →
            (∀ f₁ → script bc s f₁ ≡ script br s f₁)
reordered-≡ s br bc (dsb , ubr , ubc , pm) hf₁ with
  reordered br (reverse bc) (↭-length br↭reverse-bc) br↭reverse-bc ue
            (subst (λ x → HazardFree s br x _)
                   (sym (reverse-involutive bc)) hf₁)
  where br↭reverse-bc : br ↭ reverse bc
        br↭reverse-bc = ↭-trans (↭-sym pm) (↭-reverse bc)
        ue : UniqueEvidence br (reverse bc) []
        ue = ubr , (unique-reverse bc ubc) , [] , λ ()
... | ∀₁ = λ f₁ → subst (λ x → script x s f₁ ≡ script br s f₁)
                         (reverse-involutive bc) (sym (∀₁ f₁))
