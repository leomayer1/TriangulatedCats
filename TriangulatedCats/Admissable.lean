import TriangulatedCats.ThickSubcategory
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.Tactic.Abel

noncomputable section

open CategoryTheory Limits ObjectProperty Functor Preadditive Pretriangulated ZeroObject

open IsStableUnderShift

section sod

variable (C : Type*) [Category C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

structure SOD where
A : ThickSubcategory C
B : ThickSubcategory C
hom : ∀ b ∈ B, ∀ a ∈ A, ∀ f : b ⟶ a, f = 0
prop : ∀ x : C, ∃ b ∈ B, ∃ a ∈ A, ∃ f : b ⟶ x, ∃ g : x ⟶ a, ∃ h : a ⟶ b⟦(1 : ℤ)⟧,
  Triangle.mk f g h ∈ distTriang C

end sod


section admissible

variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

variable (A B : ThickSubcategory C) (S : SOD C) (X : C)

def IsLeftAdmissible := IsRightAdjoint (ι A.carrier)
def IsRightAdmissible := IsLeftAdjoint (ι B.carrier)


namespace SOD

open Exists

/- The projection triangle coming from an SOD -/
def Triang : Triangle C := Triangle.mk
  (choose (choose_spec (choose_spec $ S.prop X).2).2)
  (choose $ choose_spec (choose_spec (choose_spec $ S.prop X).2).2)
  (choose $ choose_spec $ choose_spec (choose_spec (choose_spec $ S.prop X).2).2)

def A_obj : C := (S.Triang X).obj₃
def B_obj : C := (S.Triang X).obj₁

def ε : X ⟶ S.A_obj X := (S.Triang X).mor₂
def η : S.B_obj X ⟶ X := (S.Triang X).mor₁

variable {S : SOD C} {X Y : C}

def Triang_dist : S.Triang X ∈ distTriang C :=
  (choose_spec $ choose_spec $ choose_spec (choose_spec (choose_spec $ S.prop X).2).2)

@[simp]
theorem B_obj_mem : S.B_obj X ∈ S.B := (choose_spec $ S.prop X).1
@[simp]
theorem Triang_obj₂ : (S.Triang X).obj₂ = X := rfl
@[simp]
theorem A_obj_mem : S.A_obj X ∈ S.A := (choose_spec (choose_spec $ S.prop X).2).1

lemma hom_A {A : C} (hA : A ∈ S.A) (f : X ⟶ A) :
    ∃! g : S.A_obj X ⟶ A, S.ε X ≫ g = f := by
  obtain ⟨(g : S.A_obj X ⟶ _), (hg : f = S.ε X ≫ g)⟩ :=
    Triangle.yoneda_exact₂ _ Triang_dist f (S.hom _ S.B_obj_mem _ hA _)
  refine ⟨g, hg.symm, fun g' hg' => ?_⟩
  have H : S.ε X ≫ (g' - g) = 0 := by
    rw [comp_sub, ←hg, ←hg', sub_self]
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ _ Triang_dist (g' - g) H
  have hk' : k = 0 := S.hom _ (S.B.shift_mem B_obj_mem) _ hA _
  rw [←sub_eq_zero, hk, hk', comp_zero]
  rfl

lemma B_hom {B : C} (hB : B ∈ S.B) (f : B ⟶ X) :
    ∃! g : B ⟶ S.B_obj X, g ≫ S.η X = f := by
  obtain ⟨(g : B ⟶ S.B_obj X), (hg : f = g ≫ S.η X)⟩ := Triangle.coyoneda_exact₂ _ Triang_dist f (S.hom _ hB _ A_obj_mem _)
  refine ⟨g, hg.symm, fun g' hg' => ?_⟩
  have H : (g' - g) ≫ S.η X = 0 := by
    rw [sub_comp, ←hg, ←hg', sub_self]
  obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ Triang_dist) (g' - g) H
  have hk' : k = 0 := S.hom _ hB _ (S.A.shift_mem A_obj_mem) _
  rw [←sub_eq_zero, hk, hk', zero_comp]
  rfl

variable (S : SOD C) (f : X ⟶ Y)

def A_map := (hom_A A_obj_mem (f ≫ S.ε Y)).choose
def B_map := (B_hom B_obj_mem (S.η X ≫ f)).choose

variable {S : SOD C} {f : X ⟶ Y}

@[reassoc (attr := simp)]
theorem A_map_prop : S.ε X ≫ S.A_map f = f ≫ S.ε Y :=
  (hom_A A_obj_mem (f ≫ S.ε Y)).choose_spec.1

@[reassoc (attr := simp)]
theorem B_map_prop : S.B_map f ≫ S.η Y = S.η X ≫ f :=
  (B_hom B_obj_mem (S.η X ≫ f)).choose_spec.1

theorem eq_A_map {g : S.A_obj X ⟶ S.A_obj Y} (h : S.ε X ≫ g = f ≫ S.ε Y) : S.A_map f = g :=
  (hom_A A_obj_mem _).unique A_map_prop h

theorem eq_B_map {g : S.B_obj X ⟶ S.B_obj Y} (h : g ≫ S.η Y = S.η X ≫ f) : S.B_map f = g :=
  (B_hom B_obj_mem _).unique B_map_prop h

theorem ε_isIso (hX : X ∈ S.A) : IsIso (S.ε X) := ⟨by
  obtain (⟨inv, h₁, _⟩) := hom_A hX (𝟙 X)
  refine ⟨inv, h₁, ?_⟩
  obtain ⟨w, _, h₂⟩ := hom_A A_obj_mem (S.ε X)
  have hw₁ : inv ≫ S.ε X = w := by
    apply h₂
    rw [←Category.assoc, h₁, Category.id_comp]
  have hw₂ : 𝟙 (S.A_obj X) = w := h₂ _ (Category.comp_id _)
  rw [hw₁, hw₂]⟩

theorem η_isIso (hX : X ∈ S.B) : IsIso (S.η X) := ⟨by
  obtain ⟨inv, h₁, _⟩ := B_hom hX (𝟙 X)
  refine ⟨inv, ?_, h₁⟩
  obtain ⟨w, _, h₂⟩ := B_hom B_obj_mem (S.η X)
  have hw₁ : S.η X ≫ inv = w := by
    apply h₂
    rw [Category.assoc, h₁, Category.comp_id]
  have hw₂ : 𝟙 (S.B_obj X) = w := h₂ _ (Category.id_comp _)
  rw [hw₁, hw₂]⟩

@[simps]
def A_func : C ⥤ FullSubcategory S.A.carrier where
  obj X := ⟨_, A_obj_mem⟩
  map f := ⟨S.A_map f⟩
  map_id X := by
    ext
    apply eq_A_map
    simp
  map_comp f g := by
    ext
    apply eq_A_map
    simp

@[simps!]
def B_func : C ⥤ FullSubcategory S.B.carrier where
  obj X := ⟨_, B_obj_mem⟩
  map f := ⟨S.B_map f⟩
  map_id X := by
    ext
    apply eq_B_map
    simp
  map_comp f g := by
    ext
    apply eq_B_map
    simp

@[simps]
def A_unit : 𝟭 C ⟶ A_func ⋙ (ι S.A.carrier) where
  app X := S.ε X

@[simps]
def A_counit : (ι S.A.carrier) ⋙ A_func ⟶ 𝟭 _ where
  app X := ⟨(inv (S.ε X.obj) (I := ε_isIso X.property))⟩

@[simps]
def B_counit : B_func ⋙ (ι S.B.carrier) ⟶ 𝟭 C where
  app X := S.η X

@[simps]
def B_unit : 𝟭 _ ⟶ (ι S.B.carrier) ⋙ B_func where
  app X := ⟨(inv (S.η X.obj) (I := η_isIso X.property))⟩
  naturality X Y f := by
    ext
    simp [←Category.assoc]


theorem isLeftAdmissible : IsLeftAdmissible S.A :=
  ⟨S.A_func, ⟨{
    unit := S.A_unit
    counit := S.A_counit
    left_triangle_components X := by
      have h : S.A_map (S.ε X) = S.ε (S.A_obj X) := by
        apply eq_A_map
        simp
      ext; simp [h]
  }⟩⟩

theorem isRightAdmissible : IsRightAdmissible S.B :=
  ⟨S.B_func, ⟨{
    unit := S.B_unit
    counit := S.B_counit
    right_triangle_components X := by
      have h : S.B_map (S.η X) = S.η (S.B_obj X) := by
        apply eq_B_map
        simp
      ext; simp [h]
  }⟩⟩

end SOD

def RightComplement (B : Set C) [IsStableUnderShift B ℤ] : ThickSubcategory C where
  carrier := {c : C | ∀ b ∈ B, ∀ f : b ⟶ c, f = 0}
  zero_mem' b hb f := zero_of_to_zero f
  shift_mem' {i} {a} ha b hb f := by
    rw [←map_eq_zero_iff (shiftFunctor C (-i)), ←IsIso.comp_right_eq_zero _ (shiftShiftNeg _ _).hom]
    apply ha (b⟦-i⟧) (le_shift B _ _ hb)
  iso_mem' {a b ha} φ c hc f := by
    rw [←IsIso.comp_right_eq_zero _ φ.inv]
    apply ha _ hc
  obj₃_mem' {T} hT hT₁ hT₂ b hb f := by
    have H : f ≫ T.mor₃ = 0 := by
      rw [←map_eq_zero_iff (shiftFunctor C (-1 : ℤ)), ←IsIso.comp_right_eq_zero _ (shiftShiftNeg _ _).hom]
      apply hT₁ _ (le_shift B _ _ hb)
    obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₃ T hT _ H
    rw [(hT₂ b hb g), zero_comp]
  smd_mem' {_ _ h} _ hb _ := zero_of_comp_mono biprod.inl (h _ hb _)

def LeftComplement (A : Set C) [IsStableUnderShift A ℤ] : ThickSubcategory C where
  carrier := {c : C | ∀ a ∈ A, ∀ f : c ⟶ a, f = 0}
  zero_mem' _ _ f := zero_of_from_zero f
  shift_mem' {i} {b} hb a ha f := by
    rw [←map_eq_zero_iff (shiftFunctor C (-i)), ←IsIso.comp_left_eq_zero  (shiftShiftNeg _ _).inv _]
    apply hb (a⟦-i⟧) (le_shift A _ _ ha)
  iso_mem' {a b ha} φ c hc f := by
    rw [←IsIso.comp_left_eq_zero φ.hom _]
    apply ha _ hc
  obj₃_mem' {T} hT hT₁ hT₂ a ha f := by
    obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ T hT f (hT₂ _ ha _)
    have hg : g = 0 := by
      rw [←map_eq_zero_iff (shiftFunctor C (-1)), ←IsIso.comp_left_eq_zero  (shiftShiftNeg _ _).inv _]
      apply hT₁ (a⟦-1⟧) (le_shift A _ _ ha)
    rw [hg, comp_zero]
  smd_mem' {_ _ h} _ hb _ := zero_of_epi_comp biprod.fst (h _ hb _)

namespace Admissible

notation "ᗮ" A => LeftComplement A
notation A "ᗮ" => RightComplement A

variable {A B : ThickSubcategory C}

def unitTriang {π : C ⥤ FullSubcategory A.carrier} (adj : π ⊣ ι A.carrier) (X : C) : Triangle C :=
  let h := distinguished_cocone_triangle₁ (adj.unit.app X)
  Triangle.mk
    (Exists.choose $ Exists.choose_spec h)
    (adj.unit.app X)
    (Exists.choose $ Exists.choose_spec $ Exists.choose_spec h)

theorem unitTriang_dist {π : C ⥤ FullSubcategory A.carrier} {adj : π ⊣ ι A.carrier} {X : C} :
    (unitTriang adj X) ∈ distTriang C :=
  let h := distinguished_cocone_triangle₁ (adj.unit.app X)
  Exists.choose_spec $ Exists.choose_spec $ Exists.choose_spec h

open Function

theorem yoneda_iso_shift {X Y Z : C} {i : ℤ} (f : X ⟶ Y)
    (hf : Bijective ((f ≫ ·) : (Y ⟶ Z) → (X ⟶ Z))) :
  Bijective ((f⟦i⟧' ≫ .) : (Y⟦i⟧ ⟶ Z⟦i⟧) → (X⟦i⟧ ⟶ Z⟦i⟧)) := sorry
/-
  Might need to give thick subcategories a triangulated category instance?
  And prove that adjoints preserve shifts and are triangulated
-/
def SOD_left (hA : IsLeftAdmissible A) : SOD C where
  A := A
  B := ᗮ A
  hom b hb a ha f := hb _ ha f
  prop := by
    obtain ⟨π, ⟨φ⟩⟩ := hA
    intro X
    obtain ⟨Xb, f, h, H⟩ := distinguished_cocone_triangle₁ (φ.unit.app X)
    use Xb
    constructor
    intro A hA s
    sorry
    refine ⟨(π.obj X).obj, (π.obj X).property, _, _, _, H⟩


def SOD_right (hB : IsRightAdmissible B) : SOD C where
  A := B
  B := B ᗮ
  hom b hb a ha f := sorry
  prop := sorry

end Admissible

end admissible
