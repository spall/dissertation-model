open import Functional.State using (Oracle ; Cmd ; FileSystem)

module Functional.Script.Hazard.Base (oracle : Oracle) where

open import Agda.Builtin.Equality
open import Functional.State.Helpers (oracle) using (cmdWriteNames ; cmdReadNames ; run)
open import Data.Bool using (true ; false)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.Product using (_×_ ; proj₁ ; proj₂ ; _,_ ; ∃-syntax)
open import Functional.File using (FileName)
open import Functional.Build (oracle) using (Build)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Common.List.Properties using (_before_∈_)
open import Function using (_∘_)
open import Data.String.Properties using (_≟_)

FileInfo : Set
FileInfo = List (Cmd × List FileName × List FileName)

-- extends FileInfo with a new entry for the Cmd
save : FileSystem → Cmd → FileInfo → FileInfo
save s x fi = (x , (cmdReadNames x s) , (cmdWriteNames x s)) ∷ fi

cmdsRun : FileInfo → List Cmd
cmdsRun = map proj₁

-- files read so far by build
filesRead : FileInfo → List FileName
filesRead = concatMap (proj₁ ∘ proj₂)

-- files written so far by build
filesWrote : FileInfo → List FileName
filesWrote = concatMap (proj₂ ∘ proj₂)

files : FileInfo → List FileName
files ls = (filesRead ls) ++ (filesWrote ls)

-- The FileNames the Cmd wrote according to the FileInfo
cmdWrote : FileInfo → Cmd → List FileName
cmdWrote [] p = []
cmdWrote (x ∷ ls) p with (proj₁ x) ≟ p
... | yes x≡p = proj₂ (proj₂ x)
... | no ¬x≡p = cmdWrote ls p

-- The FileNames the Cmd read according to the FileInfo
cmdRead : FileInfo → Cmd → List FileName
cmdRead [] p = []
cmdRead (x ∷ ls) p with (proj₁ x) ≟ p
... | yes x≡p = proj₁ (proj₂ x)
... | no ¬x≡p = cmdRead ls p

data Hazard : FileSystem → Cmd → Build → FileInfo → Set where
  ReadWrite   : ∀ {s} {x} {b} {ls} {v} → v ∈ (cmdWriteNames x s) → v ∈ (filesRead ls) →
              Hazard s x b ls
  WriteWrite  : ∀ {s} {x} {b} {ls} {v} → v ∈ (cmdWriteNames x s) → v ∈ (filesWrote ls) →
              Hazard s x b ls
  Speculative : ∀ {s} {x} {b} {ls} {v} x₁ x₂ → x₂ before x₁ ∈ (x ∷ (cmdsRun ls)) →
              x₂ ∈ b → ¬ x₁ before x₂ ∈ b → v ∈ cmdRead (save s x ls) x₂ →
              v ∈ cmdWrote (save s x ls) x₁ → Hazard s x b ls

∃Hazard : Build → Set
∃Hazard b = ∃[ sys ](∃[ x ](∃[ ls ](Hazard sys x b ls)))

data HazardFree : FileSystem → Build → Build → FileInfo → Set where
  []  : ∀ {s} {b} {ls} → HazardFree s [] b ls
  _∷_ : ∀ {s} {x} {b₁} {b₂} {ls} → ¬ Hazard s x b₂ ls →
      HazardFree (run x s) b₁ b₂ (save s x ls) → HazardFree s (x ∷ b₁) b₂ ls
