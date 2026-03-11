import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Topology.Sets.Closeds

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
iso_mem' {X Y : C} : X ∈ carrier → Nonempty (X ≅ Y) → Y ∈ carrier
obj₃_mem' {T : Triangle C} : T ∈ distTriang C → T.obj₁ ∈ carrier → T.obj₂ ∈ carrier → T.obj₃ ∈ carrier
smd_mem' {X Y : C} : (X ⊞ Y) ∈ carrier → X ∈ carrier

instance : SetLike (ThickSubcategory C) C where
  coe X := X.carrier
  coe_injective' X Y (h : X.carrier = Y.carrier) := by ext; rw [h]

variable (P : ThickSubcategory C)

end thick


namespace ThickSubcategory


variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable (P : ThickSubcategory C)

@[simp]
theorem zero_mem : 0 ∈ P := P.zero_mem'

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

theorem iso_mem {X Y : C} (hX : X ∈ P) (hXY : Nonempty (X ≅ Y)) : Y ∈ P := P.iso_mem' hX hXY

theorem obj₁_mem {T : Triangle C} (hT : T ∈ distTriang C) (h₂ : T.obj₂ ∈ P) (h₃ : T.obj₃ ∈ P) : T.obj₁ ∈ P :=
  P.mem_of_shift_mem (P.obj₃_mem' (T := T.rotate) (rot_of_distTriang T hT) h₂ h₃)

theorem obj₂_mem {T : Triangle C} (hT : T ∈ distTriang C) (h₁ : T.obj₁ ∈ P) (h₃ :T.obj₃ ∈ P) : T.obj₂ ∈ P :=
  P.obj₁_mem (T := T.rotate) (rot_of_distTriang T hT) h₃ (P.shift_mem' h₁)

theorem obj₃_mem {T : Triangle C} : T ∈ distTriang C →  T.obj₁ ∈ P → T.obj₂ ∈ P → T.obj₃ ∈ P := P.obj₃_mem'

theorem biprod_mem {X Y : C} (hX : X ∈ P) (hY : Y ∈ P) : (X ⊞ Y) ∈ P :=
  P.obj₂_mem (binaryBiproductTriangle_distinguished X Y) hX hY
theorem smd_mem_left {X Y : C} (hXY : (X ⊞ Y) ∈ P) : X ∈ P := P.smd_mem' hXY
theorem smd_mem_right {X Y : C} (hXY : (X ⊞ Y) ∈ P) : Y ∈ P := P.smd_mem' (P.iso_mem hXY ⟨biprod.braiding X Y⟩)

end ThickSubcategory


section topology


variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

def Z (I : Set C) : Set (ThickSubcategory C) := {P : (ThickSubcategory C) | I ∩ P = ⊥}

@[simp]
def mem_Z_iff {I : Set C} {P : ThickSubcategory C} : P ∈ Z I ↔ (I ∩ P) = ⊥ := by simp [Z]
def not_mem_Z_iff {I : Set C} {P : ThickSubcategory C} : P ∉ Z I ↔ ∃ X, X ∈ I ∩ P := by
  contrapose
  convert mem_Z_iff
  simp [Set.eq_empty_iff_forall_notMem]

theorem ThickSubcategory.ne_empty (P : ThickSubcategory C) : P.carrier ≠ ∅ :=
  (Set.nonempty_iff_ne_empty).mp ⟨0, P.zero_mem⟩

instance : TopologicalSpace (ThickSubcategory C) := TopologicalSpace.ofClosed {Z I | I : Set C}
    ⟨⊤, Set.eq_empty_iff_forall_notMem.mpr (fun P => by simp [Z]; apply P.ne_empty)⟩
    (by
      intro A hA
      use ⋃₀ {I | Z I ∈ A}
      ext P
      constructor
      . intro hP
        rw [Set.mem_sInter]
        rw [mem_Z_iff] at hP
        rintro X hX
        obtain ⟨I, hI⟩ := hA hX
        rw [←hI, mem_Z_iff, ←le_bot_iff]
        rw [←hI] at hX
        rw [←le_bot_iff] at hP
        apply le_trans _ hP
        apply Set.inter_subset_inter_left _ (Set.subset_sUnion_of_mem _)
        exact hX
      . intro hP
        rw [mem_Z_iff]
        rw [Set.mem_sInter] at hP
        ext X
        constructor
        . rintro ⟨hx₁, hx₂⟩
          obtain ⟨I, hZI : Z I ∈ A, hXI⟩ := hx₁
          specialize hP (Z I) hZI
          rw [mem_Z_iff] at hP
          rw [←hP]
          exact ⟨hXI, hx₂⟩
        . intro hX; cases hX
    )
    (by
      rintro _ ⟨I, rfl⟩ _ ⟨J, rfl⟩
      use {C | ∃ A ∈ I, ∃ B ∈ J, C = (A ⊞ B)}
      ext P
      constructor <;> contrapose
      . rw [←Set.mem_compl_iff, Set.compl_union]
        rintro ⟨hPI, hPJ⟩
        rw [Set.mem_compl_iff, not_mem_Z_iff] at hPI hPJ
        rw [not_mem_Z_iff]
        obtain ⟨A, hAI, hAP⟩ := hPI
        obtain ⟨B, hBJ, hBP⟩ := hPJ
        exact ⟨A ⊞ B, ⟨A, hAI, B, hBJ, rfl⟩, P.biprod_mem hAP hBP⟩
      . intro hP
        rw [not_mem_Z_iff] at hP
        rcases hP with ⟨_ ,⟨A, hAI, B, hBI, rfl⟩, hP⟩
        rw [←Set.mem_compl_iff, Set.compl_union]
        constructor <;> rw [Set.mem_compl_iff, not_mem_Z_iff]
        refine ⟨A, hAI, P.smd_mem_left hP⟩
        refine ⟨B, hBI, P.smd_mem_right hP⟩
    )

end topology

section supportdatum

open TopologicalSpace

variable (C : Type*) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

structure SupportDatum where
X : Type*
hX : TopologicalSpace X
supp : C → Closeds X
supp_zero' : supp 0 = ⊥
supp_biprod' (a b : C) : supp (a ⊞ b) = supp (a) ⊔ supp (b)
supp_shift' (a : C) : supp (a⟦(1 : ℤ)⟧) = supp (a)
supp_obj₃' {T : Triangle C} (hT : T ∈ distTriang C) : supp (T.obj₃) ≤ supp (T.obj₁) ⊔ supp (T.obj₂)

instance SupportDatum.TopologicalSpace (X : SupportDatum C) : TopologicalSpace X.X := X.hX

@[simps]
def UnivSupport : SupportDatum C where
X := ThickSubcategory C
hX := inferInstance
supp a := ⟨Z {a}, by use {a}; simp⟩
supp_zero' := by ext; simp
supp_biprod' a b := by
  ext P
  simp
  contrapose!
  exact ⟨fun h => ⟨P.smd_mem_left h, P.smd_mem_right h⟩, fun h => P.biprod_mem h.left h.right⟩
supp_shift' a := by
  ext P
  simp
  contrapose!
  refine ⟨P.mem_of_shift_mem (i := 1), P.shift_mem (i := 1)⟩
supp_obj₃' {T} hT := by
  intro P hP₃
  simp at *
  by_cases hP₁ : T.obj₁ ∈ P
  . right
    simp
    intro hP₂
    apply hP₃
    apply P.obj₃_mem hT hP₁ hP₂
  . left
    simpa

end supportdatum

namespace SupportDatum

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable (X : SupportDatum C)

example (a b : C) : a ⟶ b := 0

@[simp]
def supp_zero : X.supp 0 = ⊥ := X.supp_zero'
def supp_biprod (a b : C) : X.supp (a ⊞ b) = X.supp (a) ⊔ X.supp (b) := X.supp_biprod' a b
def supp_obj₁ {T : Triangle C} (hT : T ∈ distTriang C) : X.supp (T.obj₁) ≤ X.supp (T.obj₂) ⊔ X.supp (T.obj₃) := by
  rw [←X.supp_shift' T.obj₁]
  exact X.supp_obj₃' (T := T.rotate) (rot_of_distTriang T hT)
def supp_obj₂ {T : Triangle C} (hT : T ∈ distTriang C) : X.supp (T.obj₂) ≤ X.supp (T.obj₁) ⊔ X.supp (T.obj₃) := by
  rw [←X.supp_shift' T.obj₁, sup_comm]
  exact X.supp_obj₁ (T := T.rotate) (rot_of_distTriang T hT)
def supp_obj₃ {T : Triangle C} (hT : T ∈ distTriang C) : X.supp (T.obj₃) ≤ X.supp (T.obj₁) ⊔ X.supp (T.obj₂) := X.supp_obj₃' hT
def supp_iso {a b : C} (h : Nonempty (a ≅ b)) : X.supp a = X.supp b := by
  obtain ⟨φ⟩ := h
  let T : Triangle C := Triangle.mk (Z := 0) φ.hom 0 0
  have hT : T ∈ distTriang C := by
    apply isomorphic_distinguished (contractibleTriangle a) (contractible_distinguished a)
    apply Triangle.isoMk _ _ (Iso.refl a) (φ.symm) (Iso.refl 0)
  apply le_antisymm
  . convert X.supp_obj₁ hT
    simp [T]
  . convert X.supp_obj₂ hT
    simp [T]
@[simp]
def supp_shift {i : ℤ} (a : C) : X.supp (a⟦i⟧) = X.supp (a) := by
  induction i with
  | zero => exact X.supp_iso ⟨(shiftFunctorZero C ℤ).app a⟩
  | succ i ih =>
    rw [←ih]
    exact Eq.trans (X.supp_iso ⟨(shiftFunctorAdd' C _ _ _ rfl).app a⟩) (X.supp_shift' _)
  | pred i ih =>
    rw [←ih]
    symm
    exact Eq.trans (X.supp_iso ⟨(shiftFunctorAdd' C _ _ _ (sub_add_cancel _ _)).app a⟩) (X.supp_shift' _)

structure SupportDatumHom (X Y : SupportDatum C) where
f : X.X → Y.X
cont : Continuous f
supp : ∀ a : C, X.supp a = f⁻¹' Y.supp a

instance : Category (SupportDatum C) where
Hom X Y := SupportDatumHom X Y
id X := { f := id, cont := continuous_id, supp a := rfl}
comp {X Y Z} f g :=
  { f := g.f ∘ f.f, cont := Continuous.comp g.cont f.cont, supp a := by ext; simp [f.supp, g.supp]}

def isTerminal_UnivSupportDatum : IsTerminal (UnivSupport C) := IsTerminal.ofUniqueHom
  (fun X =>
    { f x :=
      { carrier := {a | x ∉ (X.supp a)},
        zero_mem' := by
          simp
          apply Set.notMem_empty,
        shift_mem' {i} {a} (ha : x ∉ _) := by
          rw [←X.supp_shift a] at ha
          exact ha
        iso_mem' {a} {b} (ha : x ∉ _) (h) := by
          rw [X.supp_iso h] at ha
          exact ha,
        obj₃_mem' {T} hT (h₁ : x ∉ X.supp T.obj₁) (h₂ : x ∉ X.supp T.obj₂) := by
          intro h₃
          cases X.supp_obj₃ hT h₃
          . apply h₁
            assumption
          . apply h₂
            assumption
        smd_mem' {a} {b} (hab : _ ∉ _) := by
          intro ha
          apply hab
          rw [X.supp_biprod]
          left
          exact ha
      }
      cont := by
        rw [continuous_iff_isClosed]
        intro s hs
        sorry
      supp a := sorry
    })
  sorry

end SupportDatum
