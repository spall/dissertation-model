open import Functional.State
  using (Oracle ; FileSystem ; Memory ; Cmd ; extend ; State ; save)

module Functional.Rattle.Properties (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Data.Bool using (true ; false)
open import Data.List using (List ; map ; _++_ ; foldr ; _∷_ ; [])
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻)
open import Data.List.Properties using (∷-injective)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Unary.All using (All ; lookup)
open import Data.List.Relation.Unary.AllPairs using (_∷_ ; [])
open import Data.List.Relation.Unary.Any using (tail ; here ; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (nothing ; just)
open import Data.Product.Properties using (,-injectiveʳ ; ,-injectiveˡ)
open import Data.Product using (proj₁ ; proj₂ ; _,_ ; _×_ ; ∃-syntax)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (inj₂ ; inj₁ ; _⊎_)
open import Data.Sum.Properties using (inj₂-injective)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (trans ; cong ; cong-app ; sym ; decSetoid ; subst ; inspect ; [_])
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Data.List.Membership.DecSetoid (decSetoid _≟_) using (_∈_ ; _∈?_ ; _∉_)
open import Functional.State.Helpers (oracle) as St
  using (run; cmdReadNames ; cmdWriteNames ; cmdReadWriteNames ; cmdWrites)
open import Functional.State.Properties (oracle)
  using (run-unchanged-File ; run-cong-File ; run-cong ; run-cong₂-File)
open import Functional.Forward.Exec (oracle)
  using (get ; maybeAll ; run?)
open import Functional.Rattle.Exec (oracle)
  using (rattle ; runWError ; runR ; doRunR ; rattle-unchecked ; doRunWError ; checkHazard)
open import Functional.Build (oracle)
  using (Build ; UniqueEvidence ; PreCond ; DisjointBuild ; _∷_; [])
open import Functional.Script.Exec (oracle) using (script ; buildWriteNames)
open import Functional.Script.Properties (oracle) using (disjointBuild-≡ ; reordered-≡ ; script-idempotent ; script-≡₃)
open import Functional.Script.Hazard (oracle)
  using (HazardFree ; FileInfo ; _∷_ ; []) renaming (save to rec)
open import Functional.Script.Hazard.Properties (oracle)
  using (hf-still ; hazardfree? ; hf=>disjoint-∷)
open import Data.Empty using (⊥)

-- inputs recorded in memory are accurate because
-- command doesn't change its inputs
data UnchangedInputs : FileSystem → Cmd → Set where
  ui : (s : FileSystem) → (x : Cmd) →
     (∀ f₁ → f₁ ∈ cmdReadNames x s → s f₁ ≡ St.run x s f₁) → UnchangedInputs s x

-- if the memory says a command is up to date running
-- it again will have no effect.
data MemoryProperty : Memory → Set where
 []   : MemoryProperty []
 _∷_ : ∀ {m} {s} {x} → UnchangedInputs s x → MemoryProperty m →
     MemoryProperty ((x , map (λ f₁ → f₁ , (St.run x s) f₁)
                              (cmdReadWriteNames x s)) ∷ m) 

getProperty : ∀ {mm} → (x : Cmd) → MemoryProperty mm →
            (x∈ : x ∈ map proj₁ mm) →
            ∃[ sys ](get x mm x∈ ≡ map (λ f₁ → f₁ , (St.run x sys) f₁)
                                       (cmdReadWriteNames x sys) ×
                    ∀ f₁ → f₁ ∈ cmdReadNames x sys → sys f₁ ≡ St.run x sys f₁)
getProperty x ((ui sys x₁ ∀₁) ∷ mp) x∈ with x ≟ x₁
... | yes x≡x₁ = sys , cong (λ x₂ → map (λ f₁ → f₁ , St.run x₂ sys f₁)
                                         (cmdReadWriteNames x₂ sys))
                            (sym x≡x₁) ,
                 λ f₁ x₂ → subst (λ x₃ → sys f₁ ≡ St.run x₃ sys f₁)
                                  (sym x≡x₁)
                                  (∀₁ f₁ (subst (λ x₃ → f₁ ∈ cmdReadNames x₃ sys)
                                                x≡x₁ x₂))
... | no ¬x≡x₁ = getProperty x mp (tail ¬x≡x₁ x∈)

lemma1 : ∀ (s : FileSystem) {s₁} {x} ls ls₁ → All (λ (f₁ , v₁) → s f₁ ≡ v₁) ls →
       ls ≡ map (λ f₁ → f₁ , (St.run x s₁) f₁) ls₁ →
       All (λ f₁ → s f₁ ≡ St.run x s₁ f₁) ls₁
lemma1 s [] [] all₁ ≡₁ = All.[]
lemma1 s (x₁ ∷ ls) (x ∷ ls₁) (px All.∷ all₁) ≡₁ with ∷-injective ≡₁
... | x₁≡x , ≡₂ = (trans (subst (λ x₂ → s x₂ ≡ proj₂ x₁) (,-injectiveˡ x₁≡x) px)
                         (,-injectiveʳ x₁≡x)) All.∷ (lemma1 s ls ls₁ all₁ ≡₂)

-- If a command's inputs and outputs are unchanged from when
-- it was last run, then running it will have no effect.
noEffect : ∀ {s₁} {s₂} {mm} x → (∀ f₁ → s₁ f₁ ≡ s₂ f₁) → MemoryProperty mm →
         (x∈ : x ∈ map proj₁ mm) → All (λ (f₁ , v₁) → s₂ f₁ ≡ v₁) (get x mm x∈) →
         ∀ f₁ → s₂ f₁ ≡ St.run x s₁ f₁
noEffect {s₁} {s₂} {mm} x ∀₁ mp x∈ all₁ f₁ with getProperty x mp x∈
... | s₃ , get≡ , ∀₂ with f₁ ∈? cmdWriteNames x s₁
... | no f₁∉ = trans (sym (∀₁ f₁)) (run-unchanged-File f₁ (cmdWrites x s₁) f₁∉)
... | yes f₁∈ with lemma1 s₂ (get x mm x∈) (cmdReadWriteNames x s₃) all₁ get≡
... | all₂ with proj₂ (oracle x) s₃ s₁
                      (λ f₂ x₁ → sym (trans (∀₁ f₂)
                                             (trans (lookup all₂ (∈-++⁺ˡ x₁))
                                                    (sym (∀₂ f₂ x₁)))))
... | ≡₁ = trans (lookup all₂ (∈-++⁺ʳ (cmdReadNames x s₃) f₁∈₁))
                 (subst (λ x₁ → foldr extend s₃ x₁ f₁ ≡ run x s₁ f₁)
                        (sym (cong proj₂ ≡₁))
                        (run-cong-File (cmdWrites x s₁) f₁ f₁∈))
  where f₁∈₁ : f₁ ∈ cmdWriteNames x s₃
        f₁∈₁ = subst (λ ls → f₁ ∈ ls) (sym (cong (map proj₁ ∘ proj₂) ≡₁)) f₁∈

OKBuild : State → FileInfo → Build → Build → Set
OKBuild (s , mm) ls b₁ b₂ = DisjointBuild s b₁ × MemoryProperty mm ×
                            UniqueEvidence b₁ b₂ (map proj₁ ls)

g₂ : ∀ {x} xs → x ∉ xs → All (λ y → ¬ x ≡ y) xs
g₂ [] x∉xs = All.[]
g₂ (x ∷ xs) x∉xs = (λ x₃ → x∉xs (here x₃)) All.∷ (g₂ xs λ x₃ → x∉xs (there x₃))

completeness : ∀ s br bs → PreCond s br bs → HazardFree s br bs [] →
             ∃[ st ](∃[ ls ](rattle br bs ((s , []) , []) ≡ inj₂ (st , ls)))
completeness s br bc (dsb , ubr , ubc , _) hf
  = completeness-inner (s , []) [] br bc (dsb , ([] , ubr , (ubc , ([] , λ ())))) hf
  where completeness-inner : ∀ st ls b₁ b₂ → OKBuild st ls b₁ b₂ →
                           HazardFree (proj₁ st) b₁ b₂ ls →
                           ∃[ st₁ ](∃[ ls₁ ](rattle b₁ b₂ (st , ls) ≡ inj₂ (st₁ , ls₁)))
        completeness-inner st ls [] _ (dsb , mp , (ub₁ , ub₂ , uls , dsj)) hf
          = st , ls , refl
          -- ((ds ∷ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))
        completeness-inner st@(s , mm) ls (x ∷ b₁) b₂
                           ((ds ∷ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))
                           (¬hz ∷ hf) with x ∈? map proj₁ mm
        ... | yes x∈ with maybeAll {s} (get x mm x∈)
        ... | nothing with checkHazard s x {b₂} ls
        ... | just hz = contradiction hz ¬hz
        ... | nothing = completeness-inner (doRunR (s , mm) x) (rec s x ls) b₁ b₂
                                           (dsb , mp₂ , (ub₁ , ub₂ , uls₂ , dsj₂)) hf
          where dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
                dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) ,
                                    tail (λ v≡x → lookup px (proj₁ x₁)
                                                             (sym v≡x)) (proj₂ x₁))
                uls₂ : Unique (x ∷ map proj₁ ls)
                uls₂ = g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls
                mp₂ : MemoryProperty (proj₂ (doRunR (s , mm) x))
                mp₂ = (ui s x (λ f₁ x₂ → run-unchanged-File f₁ (cmdWrites x s)
                                                          λ x₃ → ds (x₂ , x₃))) ∷ mp 
        completeness-inner st@(s , mm) ls (x ∷ b₁) b₂
                           ((x₁ ∷ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))
                           (¬hz ∷ hf) | yes x∈ | just all₁ with
                             noEffect x (λ f₁ → refl) mp x∈ all₁
        ... | ∀₁ = completeness-inner st ls b₁ b₂
                                      ((disjointBuild-≡ (St.run x s) s b₁ ∀₁ dsb) ,
                                      mp , (ub₁ , ub₂ , uls , dsj₃))  hf₂
          where dsj₃ : Disjoint b₁ (map proj₁ ls)
                dsj₃ = λ x₂ → dsj₁ (there (proj₁ x₂) , proj₂ x₂)
                dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
                dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) ,
                       tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x)) (proj₂ x₁))
                uls₂ : Unique (x ∷ map proj₁ ls)
                uls₂ = g₂ (map proj₁ ls) (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls
                hf₂ : HazardFree s b₁ b₂ ls
                hf₂ = hf-still b₁ [] ((x , cmdReadNames x s , cmdWriteNames x s) ∷ [])
                               ls (λ f₁ x₂ → sym (∀₁ f₁)) ub₁ uls₂ dsj₂ hf        
        completeness-inner st@(s , mm) ls (x ∷ b₁) b₂
                           ((ds ∷ dsb) , mp , ((px ∷ ub₁) , ub₂ , uls , dsj₁))
                           (¬hz ∷ hf) |  no x∉ with checkHazard s x {b₂} ls
        ... | just hz = contradiction hz ¬hz
        ... | nothing
          = completeness-inner (St.run x s ,
                               save x ((cmdReadNames x s) ++ (cmdWriteNames x s))
                                    (St.run x s) mm)
                               (rec s x ls) b₁ b₂
                               (dsb ,
                                (ui s x (λ f₁ x₂ → run-unchanged-File f₁ (cmdWrites x s)
                                                      λ x₃ → ds (x₂ , x₃))  ∷ mp) ,
                                (ub₁ , ub₂ , (g₂ (map proj₁ ls)
                                                 (λ x₁ → dsj₁ (here refl , x₁)) ∷ uls) ,
                                      dsj₂)) hf 
          where dsj₂ : Disjoint b₁ (x ∷ map proj₁ ls)
                dsj₂ = λ x₁ → dsj₁ (there (proj₁ x₁) ,
                                    tail (λ v≡x → lookup px (proj₁ x₁) (sym v≡x))
                                         (proj₂ x₁))

        
script≡rattle-unchecked-inner : ∀ {s₁} {s₂} m b₁ → (∀ f₁ → s₁ f₁ ≡ s₂ f₁) →
                              DisjointBuild s₂ b₁ → MemoryProperty m →
                              (∀ f₁ → script b₁ s₁ f₁ ≡
                                      proj₁ (rattle-unchecked b₁ (s₂ , m)) f₁)
script≡rattle-unchecked-inner mm [] ∀₁ dsb mp = ∀₁ 
script≡rattle-unchecked-inner {s₁} {s₂} mm (x ∷ b₁) ∀₁ (dsj ∷ dsb) mp f₁ with
  x ∈? map proj₁ mm
... | no x∉
  = script≡rattle-unchecked-inner (save x (cmdReadNames x s₂ ++ cmdWriteNames x s₂)
                                        (St.run x s₂) mm)
                                  b₁ (run-cong x ∀₁) dsb mp₁ f₁
  where mp₁ : MemoryProperty (save x (cmdReadNames x s₂ ++ cmdWriteNames x s₂)
                                   (St.run x s₂) mm)
        mp₁ = ui s₂ x (λ f₂ x₁ → run-unchanged-File f₂ (cmdWrites x s₂)
                                                     λ x₂ → dsj (x₁ , x₂)) ∷ mp
... | yes x∈ with maybeAll {s₂} (get x mm x∈)
... | nothing = script≡rattle-unchecked-inner
                  (save x (cmdReadNames x s₂ ++ cmdWriteNames x s₂)
                        (St.run x s₂) mm) b₁ (run-cong x ∀₁) dsb mp₁ f₁
  where mp₁ : MemoryProperty (save x (cmdReadNames x s₂ ++ cmdWriteNames x s₂)
                                   (St.run x s₂) mm)
        mp₁ = ui s₂ x (λ f₂ x₁ → run-unchanged-File f₂ (cmdWrites x s₂)
                                                     λ x₂ → dsj (x₁ , x₂)) ∷ mp
... | just all₁ = script≡rattle-unchecked-inner
                    mm b₁ ∀₂ (disjointBuild-≡ (St.run x s₂) s₂ b₁ ∀₃ dsb) mp f₁
  where ∀₂ : ∀ f₁ → St.run x s₁ f₁ ≡ s₂ f₁
        ∀₂ f₁ = sym (noEffect x ∀₁ mp x∈ all₁ f₁)
        ∀₃ : ∀ f₁ → s₂ f₁ ≡ St.run x s₂ f₁
        ∀₃ = noEffect x (λ f₂ → refl) mp x∈ all₁

script≡rattle-unchecked : ∀ s b → DisjointBuild s b →
                        (∀ f₁ → script b s f₁ ≡ proj₁ (rattle-unchecked b (s , [])) f₁)
script≡rattle-unchecked s b dsb
  = script≡rattle-unchecked-inner [] b (λ f₁ → refl) dsb []

doRunSoundness : ∀ st ls {st₁} {ls₁} b x →
               doRunWError {b} (st , ls) x ≡ inj₂ (st₁ , ls₁) → doRunR st x ≡ st₁
doRunSoundness st ls b x ≡₁ with checkHazard (proj₁ st) x {b} ls
... | nothing = cong proj₁ (inj₂-injective ≡₁)

runSoundness : ∀ s m ls st₁ ls₁ b x →
             runWError {b} x s m ls ≡ inj₂ (st₁ , ls₁) → runR x (s , m) ≡ st₁
runSoundness s m ls st₁ ls₁ b x ≡₁ with run? x (s , m)
... | false = cong proj₁ (inj₂-injective ≡₁)
... | true with checkHazard s x {b} ls
... | nothing = cong proj₁ (inj₂-injective ≡₁)

soundness : ∀ {s₁} {m₁} {ls} s br bs → DisjointBuild s br →
          rattle br bs ((s , []) , []) ≡ inj₂ ((s₁ , m₁) , ls) → (∀ f₁ → script br s f₁ ≡ s₁ f₁)
soundness s br bc dsb ≡₁ f₁
  = trans (script≡rattle-unchecked s br dsb f₁)
          (cong-app (,-injectiveˡ (soundness-driver (s , []) [] br bc ≡₁)) f₁)
  where soundness-driver : ∀ {st₁} {ls₁} st ls b₁ b₂ →
                         rattle b₁ b₂ (st , ls) ≡ inj₂ (st₁ , ls₁) →
                         rattle-unchecked b₁ st ≡ st₁
        soundness-driver st ls [] b₂ ≡₁ = cong proj₁ (inj₂-injective ≡₁)
        soundness-driver (s , m) ls (x ∷ b₁) b₂  ≡₁ with
          runWError {b₂} x s m ls | inspect (runWError {b₂} x s m) ls
        ... | inj₂ (st₂ , ls₂) | [ ≡₂ ] with runSoundness s m ls st₂ ls₂ b₂ x ≡₂
        ... | ≡st₂ = subst (λ x₁ → rattle-unchecked b₁ x₁ ≡ _)
                           (sym ≡st₂) (soundness-driver st₂ ls₂ b₁ b₂ ≡₁)

-- rattle produces a State and the System in that state
-- is equivalent to the one produced by script
≡toScript : FileSystem → Build → Build → Set
≡toScript s br bs = ∃[ s₁ ](∃[ m ](∃[ ls ](rattle br bs ((s , []) , []) ≡
                                  inj₂ ((s₁ , m) , ls) × ∀ f₁ → s₁ f₁ ≡ script bs s f₁)))

correct-sequential : ∀ s b → PreCond s b b → ¬ HazardFree s b b [] ⊎ ≡toScript s b b
correct-sequential s b pc with
  rattle b b ((s , []) , []) | inspect (rattle b b) ((s , []) , [])
... | inj₁ hz | [ ≡₁ ] = inj₁ g₁
  where g₁ : ¬ HazardFree s b b []
        g₁ hf with completeness s b b pc hf
        ... | a , fst , ≡₂ = contradiction (trans (sym ≡₁) ≡₂) λ ()
... | inj₂ ((s₁ , mm₁) , ls₁) | [ ≡₁ ] = inj₂ (s₁ , mm₁ , ls₁ , refl , ∀≡)
  where ∀≡ : ∀ f₁ → s₁ f₁ ≡ script b s f₁
        ∀≡ f₁ = sym (soundness s b b (proj₁ pc) ≡₁ f₁)

-- not true
correct-speculation : ∀ s br bc → PreCond s br bc →
                    ¬ HazardFree s bc bc [] ⊎ ≡toScript s br bc
correct-speculation s br bc pc = {!!}

partially-correct : ∀ s br bs → PreCond s br bs →
                  ¬ HazardFree s br bs [] ⊎ ≡toScript s br bs
partially-correct s br bs pc with hazardfree? s br bs []
... | no hz = inj₁ hz
... | yes hf₁ with completeness s br bs pc hf₁
... | (s₁ , m₁) , ls , ≡₁ = inj₂ (s₁ , m₁ , ls , ≡₁ , ∀≡)
  where ∀≡ : ∀ f₁ → s₁ f₁ ≡ script bs s f₁
        ∀≡ f₁ = sym (trans (reordered-≡ s br bs pc hf₁ f₁)
                           (soundness s br bs (proj₁ pc) ≡₁ f₁))

reordered-rattle-unchecked : ∀ s br bs → DisjointBuild s bs → PreCond s br bs →
                           HazardFree s br bs [] →
                           (∀ f₁ → proj₁ (rattle-unchecked br (s , [])) f₁ ≡
                                   proj₁ (rattle-unchecked bs (s ,  [])) f₁)
reordered-rattle-unchecked s br bs dsb pc hf f₁
  = trans (sym (script≡rattle-unchecked s br (proj₁ pc) f₁))
          (trans (sym (reordered-≡ s br bs pc hf f₁))
                 (script≡rattle-unchecked s bs dsb f₁))

preservesMemoryProperty : ∀ {s} {m} b → DisjointBuild s b → MemoryProperty m →
                        MemoryProperty (proj₂ (rattle-unchecked b (s , m)))
preservesMemoryProperty [] _ mp = mp
preservesMemoryProperty {s} {m} (x ∷ b) (dsj ∷ dsb) mp with x ∈? map proj₁ m
... | no x∉ = preservesMemoryProperty
                b dsb (ui s x (λ f₁ x₁ → run-unchanged-File f₁ (cmdWrites x s)
                                                            λ x₂ → dsj (x₁ , x₂)) ∷ mp)
... | yes x∈ with maybeAll {s} (get x m x∈)
... | nothing = preservesMemoryProperty
                  b dsb (ui s x (λ f₁ x₁ → run-unchanged-File f₁ (cmdWrites x s)
                                                            λ x₂ → dsj (x₁ , x₂)) ∷ mp)
... | just all₁ = preservesMemoryProperty
                    b (disjointBuild-≡ (St.run x s) s b
                                       (noEffect x (λ f₁ → refl) mp x∈ all₁) dsb)
                    mp


still-disjoint : ∀ {b₁} {ls} s₁ s₂ b → HazardFree s₁ b b₁ ls →
               (∀ f₁ → f₁ ∉ buildWriteNames s₁ b → s₁ f₁ ≡ s₂ f₁) →
               DisjointBuild s₁ b → DisjointBuild s₂ b
still-disjoint s₁ s₂ [] hf ∀₁ dsj = []
still-disjoint s₁ s₂ (x ∷ b) (¬hz ∷ hf) ∀₁ (dsj ∷ dsb)
    = g₀ ∷ (still-disjoint (run x s₁) (run x s₂) b hf (λ f₁ x₃ → g₁ f₁ x₃) dsb)
      where g₄ : ∀ f₁ → f₁ ∉ cmdWriteNames x s₁ →
               f₁ ∉ buildWriteNames (run x s₁) b →
               f₁ ∈ buildWriteNames s₁ (x ∷ b) → ⊥
            g₄ f₁ f₁∉₁ f₁∉₂ f₁∈ with ∈-++⁻ (cmdWriteNames x s₁) f₁∈
            ... | inj₁ ∈₁ = contradiction ∈₁ f₁∉₁
            ... | inj₂ ∈₂ = contradiction ∈₂ f₁∉₂
            g₃ : ∀ f₁ → f₁ ∈ cmdReadNames x s₁ → s₁ f₁ ≡ s₂ f₁
            g₃ f₁ f₁∈ with hf=>disjoint-∷ s₁ x b _ (¬hz ∷ hf)
            ... | dsj₂ = ∀₁ f₁ λ x₁ → g₄ f₁ (λ x₂ → dsj (f₁∈ , x₂))
                          (λ x₂ → dsj₂ (f₁∈ , x₂)) x₁
        
            g₁ : ∀ f₁ → f₁ ∉ buildWriteNames (run x s₁) b → run x s₁ f₁ ≡ run x s₂ f₁
            g₁ f₁ f₁∉ with proj₂ (oracle x) s₁ s₂ (λ f₂ x₁ → g₃ f₂ x₁)
            ... | ≡₁ with f₁ ∈? cmdWriteNames x s₁
            ... | yes f₁∈ws = subst (λ x₁ → St.run x s₁ f₁ ≡ foldr extend s₂ x₁ f₁)
                                    (cong proj₂ ≡₁)
                                    (run-cong-File (cmdWrites x s₁) f₁ f₁∈ws) 
            ... | no f₁∉ws = run-cong₂-File ≡₁ (∀₁ f₁ λ x₁ → g₄ f₁ f₁∉ws f₁∉ x₁)
            g₀ : Disjoint (cmdReadNames x s₂) (cmdWriteNames x s₂)
            g₀ x₁ with proj₂ (oracle x) s₁ s₂ (λ f₂ x₁ → g₃ f₂ x₁)
            ... | ≡₁ = dsj (subst (λ x₂ → _ ∈ x₂)
                                  (cong (map proj₁ ∘ proj₁) (sym ≡₁)) (proj₁ x₁)
                          , subst (λ x₂ → _ ∈ x₂)
                                  (cong (map proj₁ ∘ proj₂) (sym ≡₁)) (proj₂ x₁))

rattle-idempotent : ∀ s b {b₁} → DisjointBuild s b → HazardFree s b b₁ [] →
                  (∀ f₁ → proj₁ (rattle-unchecked b (s , [])) f₁ ≡
                          proj₁ (rattle-unchecked b (rattle-unchecked b (s , []))) f₁)
rattle-idempotent s b dsb hf f₁ with
  rattle-unchecked b (s , []) | inspect (rattle-unchecked b) (s , []) |
  script≡rattle-unchecked s b dsb 
... | (s₁ , m₁) | [ ≡₂ ] | ≡₁
  = trans (sym (≡₁ f₁))
          (trans (script-idempotent s b dsb hf f₁)
                 (script≡rattle-unchecked-inner m₁ b ≡₁
                   (still-disjoint s s₁ b hf
                                   (λ f₂ x → trans (sym (script-≡₃ s b x))
                                                    (≡₁ f₂)) dsb)
                   (subst (λ x → MemoryProperty x) (cong proj₂ ≡₂)
                          (preservesMemoryProperty b dsb []))
                   f₁))
