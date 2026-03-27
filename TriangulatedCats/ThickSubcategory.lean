import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
/-
  Define basic definitions for Matsui spectra
  · thick subcategories
  · topology instance on Th(C)
  · support datum
  · proof that Th(C) is final among support data
-/


open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject

section thick

variable (C : Type*) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

@[ext]
structure ThickSubcategory where
carrier : Set C
zero_mem' : 0 ∈ carrier
shift_mem' {i : ℤ} {X : C} : X ∈ carrier → (X⟦i⟧) ∈ carrier
iso_mem' {X Y : C} : X ∈ carrier → (X ≅ Y) → Y ∈ carrier
obj₃_mem' {T : Triangle C} : T ∈ distTriang C → T.obj₁ ∈ carrier → T.obj₂ ∈ carrier → T.obj₃ ∈ carrier
smd_mem' {X Y : C} : (X ⊞ Y) ∈ carrier → X ∈ carrier

instance : SetLike (ThickSubcategory C) C where
  coe X := X.carrier
  coe_injective' X Y (h : X.carrier = Y.carrier) := by ext; rw [h]

end thick


namespace ThickSubcategory


variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [HasZeroObject C]
  [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated C] [Pretriangulated D]
variable (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
variable (P : ThickSubcategory C)

@[simp]
theorem zero_mem : 0 ∈ P := P.zero_mem'

theorem shift_mem {i : ℤ} {X : C} (hX : X ∈ P) : X⟦i⟧ ∈ P := P.shift_mem' hX
theorem mem_of_shift_mem {i : ℤ} {X : C} (hX : X⟦i⟧ ∈ P) : X ∈ P := by
  refine P.iso_mem' (?_ : X⟦i⟧⟦-i⟧ ∈ P) (?_)
  apply P.shift_mem' hX
  trans
  symm
  exact (shiftFunctorAdd C (i) (-i)).app X
  rw [add_neg_cancel]
  exact (shiftFunctorZero C ℤ).app X

theorem iso_mem {X Y : C} (hX : X ∈ P) (hXY : X ≅ Y) : Y ∈ P := P.iso_mem' hX hXY

theorem obj₁_mem {T : Triangle C} (hT : T ∈ distTriang C) (h₂ : T.obj₂ ∈ P) (h₃ : T.obj₃ ∈ P) : T.obj₁ ∈ P :=
  P.mem_of_shift_mem (P.obj₃_mem' (T := T.rotate) (rot_of_distTriang T hT) h₂ h₃)

theorem obj₂_mem {T : Triangle C} (hT : T ∈ distTriang C) (h₁ : T.obj₁ ∈ P) (h₃ :T.obj₃ ∈ P) : T.obj₂ ∈ P :=
  P.obj₁_mem (T := T.rotate) (rot_of_distTriang T hT) h₃ (P.shift_mem' h₁)

theorem obj₃_mem {T : Triangle C} : T ∈ distTriang C →  T.obj₁ ∈ P → T.obj₂ ∈ P → T.obj₃ ∈ P := P.obj₃_mem'

theorem biprod_mem {X Y : C} (hX : X ∈ P) (hY : Y ∈ P) : (X ⊞ Y) ∈ P :=
  P.obj₂_mem (binaryBiproductTriangle_distinguished X Y) hX hY
theorem smd_mem_left {X Y : C} (hXY : (X ⊞ Y) ∈ P) : X ∈ P := P.smd_mem' hXY
theorem smd_mem_right {X Y : C} (hXY : (X ⊞ Y) ∈ P) : Y ∈ P := P.smd_mem' (P.iso_mem hXY (biprod.braiding X Y))

def kernel : ThickSubcategory C where
  carrier := F.kernel
  zero_mem' := Functor.map_isZero _ (isZero_zero C)
  shift_mem' {i} X hX := IsZero.of_iso (Functor.map_isZero _ hX) ((F.commShiftIso i).app _)
  iso_mem' hX := fun φ => IsZero.of_iso hX (F.mapIso φ.symm)
  obj₃_mem' {T} hT hT₁ hT₂ := (F.mapTriangle.obj T).isZero₃_of_isZero₁₂
    (F.map_distinguished _ hT) hT₁ hT₂
  smd_mem' {X Y} hXY := by
    have := preservesBinaryBiproducts_of_preservesBinaryProducts F --why is this only a local instance?
    exact ((biprod_isZero_iff _ (F.obj Y)).mp (IsZero.of_iso hXY (Functor.mapBiprod F _ _).symm)).1

end ThickSubcategory
