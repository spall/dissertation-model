module Functional.State where

open import Agda.Builtin.Equality
open import Data.Bool using (if_then_else_)
open import Data.List using (List ; map ; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; Σ-syntax)
open import Data.String using (String ; _==_)
open import Functional.File using (File ; FileName ; FileContent)

FileSystem : Set
FileSystem = FileName -> Maybe FileContent

Cmd : Set
Cmd = String

CmdFunction : Set
CmdFunction = FileSystem → List File × List File

-- names of files read according to cmdFunction
reads : CmdFunction → FileSystem → List FileName
reads f s = map proj₁ (proj₁ (f s))

CmdProof : CmdFunction → Set
CmdProof f = ∀ s₁ s₂ → (∀ g₁ → g₁ ∈ reads f s₁ → s₁ g₁ ≡ s₂ g₁) → f s₁ ≡ f s₂

Oracle : Set
Oracle = Cmd -> Σ[ f ∈ CmdFunction ](CmdProof f)

MaybeFile : Set
MaybeFile = FileName × Maybe FileContent

Memory : Set
Memory = List (Cmd × List MaybeFile)

extend : File -> FileSystem -> FileSystem
extend (k , v) st = \ k₁ -> if (k == k₁) then just v else st k₁

save : Cmd -> List FileName -> FileSystem -> Memory -> Memory
save cmd files sys mm = (cmd , map (\f -> f , sys f) files) ∷ mm

State : Set
State = (FileSystem × Memory)
