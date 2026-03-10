import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Topology.Basic

/-
  Define basic definitions for Matsui spectra
  · thick subcategories
  · topology instance on Th(C)
  · support datum
-/

section thick

open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject


variable (C : Type*) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

@[ext]
structure ThickSubcategory where
carrier : Set C
zero_mem' : 0 ∈ carrier
shift_mem' {i : ℤ} {X : C} : X ∈ carrier → (X⟦i⟧) ∈ carrier
iso_mem' {X Y : C} : X ∈ carrier → Nonempty (X ≅ Y) → Y ∈ carrier
obj₃_mem' {T : Triangle C} : T ∈ distTriang C → T.obj₁ ∈ carrier → T.obj₂ ∈ carrier → T.obj₃ ∈ carrier
smd_mem' {X Y : C} : (X ⊞ Y) ∈ carrier → X ∈ carrier

instance : SetLike (ThickSubcategory C) C where
  coe X := X.carrier
  coe_injective' X Y (h : X.carrier = Y.carrier) := by ext; rw [h]

variable (P : ThickSubcategory C)

end thick


namespace ThickSubcategory

open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject


variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable (P : ThickSubcategory C)

@[simp]
theorem zero_mem : 0 ∈ P := P.zero_mem'
@[simp]
theorem shift_mem {i : ℤ} {X : C} (hX : X ∈ P) : X⟦i⟧ ∈ P := P.shift_mem' hX
theorem mem_of_shift_mem {i : ℤ} {X : C} (hX : X⟦i⟧ ∈ P) : X ∈ P := by
  refine P.iso_mem' (?_ : X⟦i⟧⟦-i⟧ ∈ P) (?_)
  apply P.shift_mem' hX
  constructor
  trans
  symm
  exact (shiftFunctorAdd C (i) (-i)).app X
  rw [add_neg_cancel]
  exact (shiftFunctorZero C ℤ).app X
@[simp]
theorem iso_mem {X Y : C} (hX : X ∈ P) (hXY : Nonempty (X ≅ Y)) : Y ∈ P := P.iso_mem' hX hXY
@[simp]
theorem obj₁_mem {T : Triangle C} (hT : T ∈ distTriang C) (h₂ : T.obj₂ ∈ P) (h₃ : T.obj₃ ∈ P) : T.obj₁ ∈ P :=
  P.mem_of_shift_mem (P.obj₃_mem' (T := T.rotate) (rot_of_distTriang T hT) h₂ h₃)
@[simp]
theorem obj₂_mem {T : Triangle C} (hT : T ∈ distTriang C) (h₁ : T.obj₁ ∈ P) (h₃ :T.obj₃ ∈ P) : T.obj₂ ∈ P :=
  P.obj₁_mem (T := T.rotate) (rot_of_distTriang T hT) h₃ (P.shift_mem' h₁)
@[simp]
theorem obj₃_mem {T : Triangle C} : T ∈ distTriang C →  T.obj₁ ∈ P → T.obj₂ ∈ P → T.obj₃ ∈ P := P.obj₃_mem'
@[simp]
theorem smd_mem {X Y : C} : (X ⊞ Y) ∈ P → X ∈ P := P.smd_mem'

end ThickSubcategory


section topology

open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

def Z (I : Set C) : Set (ThickSubcategory C) := {P : (ThickSubcategory C) | I ∩ P = ⊥}

theorem ThickSubcategory.ne_empty (P : ThickSubcategory C) : P.carrier ≠ ∅ :=
  (Set.nonempty_iff_ne_empty).mp ⟨0, P.zero_mem⟩

instance : TopologicalSpace (ThickSubcategory C) := TopologicalSpace.ofClosed {Z I | I : Set C}
    ⟨⊤, Set.eq_empty_iff_forall_notMem.mpr (fun P => by simp? [Z]; apply P.ne_empty)⟩
    (sorry)
    (sorry)

end topology
