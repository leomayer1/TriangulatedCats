import TriangulatedCats.ThickSubcategory
import Mathlib.Topology.Sets.Closeds
import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-
  Define basic definitions for Matsui spectra
  · thick subcategories
  · topology instance on Th(C)
  · support datum
  · proof that Th(C) is final among support data
-/


open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject

section topology


variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

def Z (I : Set C) : Set (ThickSubcategory C) := {P : (ThickSubcategory C) | I ∩ P = ⊥}
def D (I : Set C) : Set (ThickSubcategory C) := {P : (ThickSubcategory C) | ∃ X : C, X ∈ (I ∩ P)}

@[simp]
theorem mem_Z_iff {I : Set C} {P : ThickSubcategory C} : P ∈ Z I ↔ (I ∩ P) = ⊥ := by simp [Z]
theorem not_mem_Z_iff {I : Set C} {P : ThickSubcategory C} : P ∉ Z I ↔ ∃ X, X ∈ I ∩ P := by
  contrapose
  convert mem_Z_iff
  simp [Set.eq_empty_iff_forall_notMem]

theorem ThickSubcategory.ne_empty (P : ThickSubcategory C) : P.carrier ≠ ∅ :=
  (Set.nonempty_iff_ne_empty).mp ⟨0, P.zero_mem⟩


instance : TopologicalSpace (ThickSubcategory C) where
  IsOpen := {D I | I : Set C}
  isOpen_univ := ⟨⊤, Set.eq_univ_of_forall (fun P => ⟨0, Set.mem_univ _, P.zero_mem⟩)⟩
  isOpen_inter := by
    rintro _ _ ⟨I, rfl⟩ ⟨J, rfl⟩
    use {C | ∃ A ∈ I, ∃ B ∈ J, C = (A ⊞ B)}
    ext P
    constructor
    . exact fun ⟨_, ⟨⟨A, hA, B, hB, rfl⟩, hXP⟩⟩ => ⟨⟨A, hA, P.smd_mem_left hXP⟩, ⟨B, hB, P.smd_mem_right hXP⟩⟩
    . exact fun ⟨⟨A, hAI, hAP⟩, ⟨B, hBI, hBP⟩⟩ => ⟨A ⊞ B, ⟨A, hAI, B, hBI, rfl⟩, P.biprod_mem hAP hBP⟩
  isOpen_sUnion := by
    intro A hA
    use ⋃₀ {I | D I ∈ A}
    ext P
    constructor
    . exact fun ⟨X, ⟨I, hI, hIP⟩, hXP⟩ => ⟨D I, hI, ⟨X, hIP, hXP⟩⟩
    . rintro ⟨I, hI, hIP⟩
      obtain ⟨J, hJ⟩ := hA I hI
      rw [←hJ] at hIP hI
      obtain ⟨X, hX, hXP⟩ := hIP
      exact ⟨X, ⟨J, hI, hX⟩, hXP⟩

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
abbrev UnivSupport : SupportDatum C where
X := ThickSubcategory C
hX := inferInstance
supp a := ⟨{P | a ∉ P}, by use {a}; ext; simp [D]⟩
supp_zero' := by simp; rfl
supp_biprod' a b := by
  ext P
  show (a ⊞ b) ∉ P ↔ a ∉ P ∨ b ∉ P
  contrapose!
  exact ⟨fun h => ⟨P.smd_mem_left h, P.smd_mem_right h⟩, fun h => P.biprod_mem h.left h.right⟩
supp_shift' a := by
  ext P
  show (shiftFunctor C 1).obj a ∉ P ↔ a ∉ P
  contrapose!
  refine ⟨P.mem_of_shift_mem (i := 1), P.shift_mem (i := 1)⟩
supp_obj₃' {T} hT P hP₃ := by
  by_cases hP₁ : T.obj₁ ∈ P
  . exact Or.inr (fun hP₂ => hP₃ (P.obj₃_mem hT hP₁ hP₂))
  . exact Or.inl hP₁

end supportdatum

namespace SupportDatum

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable (X Y : SupportDatum C)

@[simp]
theorem supp_zero : X.supp 0 = ⊥ := X.supp_zero'
theorem supp_biprod (a b : C) : X.supp (a ⊞ b) = X.supp (a) ⊔ X.supp (b) := X.supp_biprod' a b
theorem supp_obj₁ {T : Triangle C} (hT : T ∈ distTriang C) : X.supp (T.obj₁) ≤ X.supp (T.obj₂) ⊔ X.supp (T.obj₃) := by
  rw [←X.supp_shift' T.obj₁]
  exact X.supp_obj₃' (T := T.rotate) (rot_of_distTriang T hT)
theorem supp_obj₂ {T : Triangle C} (hT : T ∈ distTriang C) : X.supp (T.obj₂) ≤ X.supp (T.obj₁) ⊔ X.supp (T.obj₃) := by
  rw [←X.supp_shift' T.obj₁, sup_comm]
  exact X.supp_obj₁ (T := T.rotate) (rot_of_distTriang T hT)
theorem supp_obj₃ {T : Triangle C} (hT : T ∈ distTriang C) : X.supp (T.obj₃) ≤ X.supp (T.obj₁) ⊔ X.supp (T.obj₂) := X.supp_obj₃' hT
theorem supp_iso {a b : C} (h : Nonempty (a ≅ b)) : X.supp a = X.supp b := by
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
theorem supp_shift {i : ℤ} (a : C) : X.supp (a⟦i⟧) = X.supp (a) := by
  induction i with
  | zero => exact X.supp_iso ⟨(shiftFunctorZero C ℤ).app a⟩
  | succ i ih =>
    rw [←ih]
    exact Eq.trans (X.supp_iso ⟨(shiftFunctorAdd' C _ _ _ rfl).app a⟩) (X.supp_shift' _)
  | pred i ih =>
    rw [←ih]
    symm
    exact Eq.trans (X.supp_iso ⟨(shiftFunctorAdd' C _ _ _ (sub_add_cancel _ _)).app a⟩) (X.supp_shift' _)

@[ext]
structure SupportDatumHom (X Y : SupportDatum C) where
f : X.X → Y.X
cont : Continuous f
supp : ∀ a : C, X.supp a = f⁻¹' Y.supp a

instance : FunLike (SupportDatumHom X Y) X.X Y.X where
  coe f := f.f
  coe_injective' a b (h : a.f = b.f) := by ext; rw [h]

instance : Category (SupportDatum C) where
Hom X Y := SupportDatumHom X Y
id X := { f := id, cont := continuous_id, supp a := rfl}
comp {X Y Z} f g :=
  { f := g.f ∘ f.f, cont := Continuous.comp g.cont f.cont, supp a := by ext; simp [f.supp, g.supp]}

instance : ConcreteCategory (SupportDatum C) SupportDatumHom where
  hom := id
  ofHom := id

def isTerminal_UnivSupportDatum : IsTerminal (UnivSupport C) := IsTerminal.ofUniqueHom
  (fun X =>
    { f x :=
      { carrier := {a | x ∉ (X.supp a)},
        zero_mem' : x ∉ X.supp 0 := by
          rw [X.supp_zero]
          apply Set.notMem_empty
        shift_mem' {i} {a} ha := by
          show x ∉ X.supp (a⟦i⟧)
          rwa [X.supp_shift a]
        iso_mem' {a} {b} (ha : x ∉ _) h := by
          show x ∉ X.supp b
          rwa [←X.supp_iso h]
        obj₃_mem' {T} hT (h₁ : x ∉ X.supp T.obj₁) (h₂ : x ∉ X.supp T.obj₂) h₃ :=
          Or.elim (X.supp_obj₃ hT h₃) h₁ h₂
        smd_mem' {a} {b} (hab : _ ∉ _) := by
          show x ∉ X.supp a
          rw [X.supp_biprod] at hab
          exact fun ha => hab (Or.inl ha)
      }
      cont := ⟨by
        rintro _ ⟨I, rfl⟩
        apply isClosed_compl_iff.mp
        have H : IsClosed (⋂₀ {(X.supp a).carrier | a ∈ I}) := by
          apply isClosed_sInter
          rintro _ ⟨a, ha, rfl⟩
          exact (X.supp a).isClosed
        convert H
        ext x
        simp [D]
        show (∀ a ∈ I, ¬(x ∉ X.supp a)) ↔ ∀ a ∈ I, x ∈ X.supp a
        aesop⟩
      supp a := Set.ext (fun x => (by tauto : x ∈ X.supp a ↔ ¬ x ∉ X.supp a))
    })
  (fun X m => by
    ext x a
    show a ∈ m.f x ↔ x ∉ (X.supp a : Set X.X)
    rw [m.supp]
    simp
  )

end SupportDatum
