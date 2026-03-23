import TriangulatedCats.ThickSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Shift


open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject ObjectProperty

section defs

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable (I J K : Set C)

inductive addc : Set C
| zero : addc 0
| of_mem {a : C} : I a → addc a
| of_shift {i : ℤ} {a : C} : addc a → addc (a⟦i⟧)
| of_iso {a b : C} : addc a → Nonempty (a ≅ b) → addc b
| biprod {a b : C} : addc a → addc b → addc (a ⊞ b)

inductive smd : Set C
| of_mem {a : C} : I a → smd a
| of_smd_left {a b : C} : smd (a ⊞ b) → smd a
| of_smd_right {a b : C} : smd (a ⊞ b) → smd b

def star' : Set C :=
  {c | ∃ a ∈ I, ∃ b ∈ J, ∃ f : a ⟶ c, ∃ g : c ⟶ b, ∃ h : b ⟶ a⟦1⟧, Triangle.mk f g h ∈ distTriang C}

infixl:60 " ⋆ " => star'

def star_assoc [IsTriangulated C] : I ⋆ J ⋆ K = I ⋆ (J ⋆ K) := by
  ext c
  constructor
  . rintro ⟨b₁, ⟨a₁, ha₁, a₂, ha₂, f', g', h', H'⟩, b₂, hb₂, f, g, h, H⟩
    obtain ⟨c₂, f'', g'', H''⟩ := distinguished_cocone_triangle (f' ≫ f)
    obtain ⟨O⟩ := IsTriangulated.octahedron_axiom (rfl) H' H H''
    refine ⟨a₁, ha₁, c₂, ⟨a₂, ha₂, b₂, hb₂, _, _, _, O.mem⟩, _, _, _, H''⟩
  /- This proof of the reserve direction gave me nightmares -/
  . rintro ⟨b₁, hb₁, b₂, ⟨a₁, ha₁, a₂, ha₂, f', g', h', H'⟩, f, g, h, H⟩
    obtain ⟨c₂, h'', f'', H''⟩ := distinguished_cocone_triangle (g ≫ g')
    obtain ⟨O⟩ := IsTriangulated.octahedron_axiom (rfl) (rot_of_distTriang _ H) (rot_of_distTriang _ H') (H'')
    refine ⟨c₂⟦-1⟧, ⟨b₁, hb₁, a₁, ha₁, ?_, ?_, f' ≫ h, ?_⟩, a₂, ha₂, _, _, _, inv_rot_of_distTriang _ H''⟩
    . exact -(shiftShiftNeg _ _).inv ≫ (O.m₁⟦-1⟧')
    . exact -(O.m₃⟦-1⟧') ≫ (shiftShiftNeg _ _).hom
    . apply isomorphic_distinguished _ (Triangle.shift_distinguished _ O.mem (-1))
      apply Triangle.isoMk _ _ (shiftShiftNeg b₁ (1 : ℤ)).symm (Iso.refl (c₂⟦-1⟧)) (shiftShiftNeg a₁ (1 : ℤ)).symm
        (comm₃ := by
          simp
          show f' ≫ h ≫ ((shiftFunctorCompIsoId C 1 (-1) _).inv.app b₁)⟦(1 : ℤ)⟧' =
            (shiftFunctorCompIsoId C 1 (-1) _).inv.app a₁ ≫ f'⟦(1:ℤ)⟧'⟦-1⟧' ≫ h⟦(1 : ℤ)⟧'⟦-1⟧' ≫
            (shiftFunctorComm C 1 (-1)).hom.app (b₁⟦1⟧)
          have HH (hh) (hh'): ((shiftFunctorCompIsoId C 1 (-1) hh).inv.app b₁)⟦(1 : ℤ)⟧' =
            (shiftFunctorCompIsoId C 1 (-1) hh').inv.app (b₁⟦(1 : ℤ)⟧) ≫ (shiftFunctorComm C 1 (-1)).hom.app (b₁⟦1⟧) := by
              rw [shift_shiftFunctorCompIsoId_inv_app]
              simp [shiftFunctorCompIsoId, shiftFunctorComm]
              rw [←assoc]
              convert (id_comp _).symm
              rw [←NatTrans.comp_app, ← shiftFunctorAdd'_eq_shiftFunctorAdd]
              simp
          rw [HH (add_neg_cancel _) (add_neg_cancel _),←assoc,←assoc,←assoc,←assoc]
          congr 1
          nth_rewrite 2 [assoc]
          rw [←Functor.map_comp, ←Functor.map_comp]
          apply NatTrans.naturality (shiftFunctorCompIsoId C 1 (-1) _).inv
        )

abbrev dia : Set C := smd (star' (addc I) (addc J))

infixl:60 " ⋄ " => dia

abbrev level : ℕ → Set C
| 0 => smd (addc {0})
| (n + 1) => level n ⋄ I

notation " ⟪" I "⟫' " n => level I n

def thick_cl' : Set C := ⋃ n : ℕ, level I n

notation " ⟪" I "⟫ " => thick_cl' I

def is_generator (G : C) := ⟪{G}⟫ = ⊤

end defs

section props

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]
variable {I J K : Set C}
variable (n m : ℕ)

theorem subset_smd : I ⊆ smd I := fun _ hx => smd.of_mem hx
theorem subset_addc : I ⊆ addc I := fun _ hx => addc.of_mem hx

theorem dia.zero : 0 ∈ I ⋄ J :=
  smd.of_mem ⟨0, addc.zero, 0, addc.zero, _, _, _, contractible_distinguished (0 : C)⟩

theorem addc_mono : Monotone (addc (C := C)) := by
  intro I J hIJ a ha
  induction ha with
  | zero => exact addc.zero
  | of_mem ha => exact addc.of_mem (hIJ ha)
  | of_shift ha ih => exact addc.of_shift ih
  | of_iso ha hab ih => exact addc.of_iso ih hab
  | biprod _ _ iha ihb => exact addc.biprod iha ihb

theorem smd_mono : Monotone (smd (C := C)) := by
  intro I J hIJ a ha
  induction ha with
  | of_mem ha => exact smd.of_mem (hIJ ha)
  | of_smd_left _ ih => exact smd.of_smd_left ih
  | of_smd_right _ ih => exact smd.of_smd_right ih

theorem star_mono {I I' J J' : Set C} (hI : I ≤ I') (hJ : J ≤ J') : I ⋆ J ≤ I' ⋆ J' := by
  rintro X ⟨a, ha, b, hb, f, g, h, H⟩
  exact ⟨a, hI ha, b, hJ hb, f, g, h, H⟩

theorem dia_mono {I I' J J' : Set C} (hI : I ≤ I') (hJ : J ≤ J') : I ⋄ J ≤ I' ⋄ J' :=
  smd_mono (star_mono (addc_mono hI) (addc_mono hJ))

theorem subset_dia_left : I ⊆ I ⋄ J := le_trans (subset_smd) (smd_mono
  (fun x hx => ⟨x, addc.of_mem hx, 0, addc.zero, _, _, _, contractible_distinguished x⟩))

theorem subset_dia_right : J ⊆ I ⋄ J := le_trans (subset_smd) (smd_mono
  (fun x hx => ⟨0, addc.zero, x, addc.of_mem hx, _, _, _, contractible_distinguished₁ x⟩))

theorem level_mono : Monotone (level I) := monotone_nat_of_le_succ (fun _ => subset_dia_left)

theorem level_mono' (h : I ≤ J) (n : ℕ) : (⟪I⟫' n) ≤ ⟪J⟫' n := by
  induction n with
  | zero => rfl
  | succ n ih => exact dia_mono ih h

theorem thick_cl_mono (h : I ≤ J) : ⟪I⟫ ≤ ⟪J⟫ := Set.iUnion_mono (fun _ => level_mono' h _)

open IsClosedUnderIsomorphisms
open IsStableUnderShift

instance : IsClosedUnderIsomorphisms (addc I) := ⟨fun φ ha => addc.of_iso ha ⟨φ⟩⟩
instance [IsClosedUnderIsomorphisms I] : IsClosedUnderIsomorphisms (smd I) := by
  refine ⟨fun {X Y} φ ha => ?_⟩
  induction ha generalizing Y with
  | of_mem h => exact smd.of_mem (of_iso φ h)
  | of_smd_left _ ih => exact smd.of_smd_left (ih (biprod.mapIso φ (Iso.refl _)))
  | of_smd_right _ ih => exact smd.of_smd_right (ih (biprod.mapIso (Iso.refl _) φ))

instance : IsStableUnderShift (addc I) ℤ := ⟨fun _ => ⟨fun _ ha => addc.of_shift ha⟩⟩
instance [IsClosedUnderIsomorphisms I] [IsStableUnderShift I ℤ] : IsStableUnderShift (smd I) ℤ := by
  refine ⟨fun i => ⟨fun a ha => ?_⟩⟩
  have := preservesBinaryBiproducts_of_preservesBinaryProducts (shiftFunctor C i)
  induction ha with
  | of_mem h => exact smd.of_mem (le_shift _ _ _ h)
  | of_smd_left _ ih => exact smd.of_smd_left (of_iso (Functor.mapBiprod _ _ _) ih)
  | of_smd_right _ ih => exact smd.of_smd_right (of_iso (Functor.mapBiprod _ _ _) ih)

instance : IsClosedUnderIsomorphisms (I ⋆ J) := ⟨by
  rintro c c' φ ⟨a, ha, b, hb, f, g, h, H⟩
  refine ⟨a, ha, b, hb, f ≫ φ.hom, φ.inv ≫ g, h, ?_⟩
  exact isomorphic_distinguished _ H _ (Triangle.isoMk _ _ (Iso.refl a) φ.symm (Iso.refl b))⟩

instance [IsStableUnderShift I ℤ] [IsStableUnderShift J ℤ] : IsStableUnderShift (I ⋆ J) ℤ :=
  ⟨fun i => ⟨by
    rintro c ⟨a, ha, b, hb, f, g, h, H⟩
    refine ⟨a⟦i⟧, ?_, b⟦i⟧, ?_, _, _, _, Triangle.shift_distinguished _ H i⟩
    exact le_shift I i a ha
    exact le_shift J i b hb⟩⟩

theorem star_eq₂ : I ⋆ J = {c | ∃ a ∈ I, ∃ b ∈ J, ∃ f : a ⟶ c, ∃ g : c ⟶ b, ∃ h : b ⟶ a⟦1⟧,
    Triangle.mk f g h ∈ distTriang C} := rfl

theorem star_eq₁ [IsStableUnderShift I ℤ] : I ⋆ J = {c | ∃ b ∈ J, ∃ a ∈ I,
    ∃ f : c ⟶ b, ∃ g : b ⟶ a, ∃ h : a ⟶ c⟦1⟧, Triangle.mk f g h ∈ distTriang C} := by
  ext
  constructor
  . rintro ⟨a, ha, b, hb, f, g, h, H⟩
    exact ⟨b, hb, a⟦(1 : ℤ)⟧, le_shift I _ _ ha, _, _, _, rot_of_distTriang _ H⟩
  . rintro ⟨b, hb, a, ha, f, g, h, H⟩
    exact ⟨a⟦-1⟧, le_shift I _ _ ha, b, hb, _, _, _, inv_rot_of_distTriang _ H⟩

theorem star_eq₃ [IsStableUnderShift J ℤ] : I ⋆ J = {c | ∃ b ∈ J, ∃ a ∈ I,
    ∃ f : b ⟶ a, ∃ g : a ⟶ c, ∃ h : c ⟶ b⟦1⟧, Triangle.mk f g h ∈ distTriang C} := by
  ext
  constructor
  . rintro ⟨a, ha, b, hb, f, g, h, H⟩
    exact ⟨b⟦-1⟧, le_shift J _ _ hb, a, ha, _, _, _, inv_rot_of_distTriang _ H⟩
  . rintro ⟨b, hb, a, ha, f, g, h, H⟩
    exact ⟨a, ha, b⟦(1 : ℤ)⟧, le_shift J _ _ hb, _, _, _, rot_of_distTriang _ H⟩

theorem level_of_smd_left {a b : C} (hab : (a ⊞ b) ∈ (⟪I⟫' n)) : a ∈ ⟪I⟫' n := by
  cases n <;> exact smd.of_smd_left hab

instance : IsClosedUnderIsomorphisms (⟪I⟫' n) := by cases n <;> infer_instance
instance : IsStableUnderShift (⟪I⟫' n) ℤ := by cases n <;> infer_instance

theorem level_star_level : (level I n) ⋆ (level I m) ≤ level I (n + m) := by
  sorry

theorem level_level : level (level I n) m = level I (n * m) := by
  sorry

def ThickSubcategory.thick_cl (I : Set C) : ThickSubcategory C where
  carrier := thick_cl' I
  zero_mem' := ⟨_, ⟨0, rfl⟩, smd.of_mem (addc.of_mem rfl)⟩
  shift_mem' {i a} := fun ⟨_, ⟨n, rfl⟩, ha⟩ => ⟨_, ⟨n, rfl⟩, le_shift (⟪I⟫' n) _ _ ha⟩
  iso_mem' {a b} := fun ⟨_, ⟨n, rfl⟩, ha⟩ ⟨φ⟩ => ⟨_, ⟨n, rfl⟩, of_iso (P := ⟪I⟫' n) φ ha⟩
  obj₃_mem' hT := sorry
  smd_mem' {a b} := fun ⟨_, ⟨n, rfl⟩, ha⟩ => ⟨_, ⟨n, rfl⟩, level_of_smd_left n ha⟩


end props

/- 3-19 TODO
  · G generator ↔ ∀ support datum supp G = supp T
  · Def of dimension
  · Dense Functors and dimension decreasing

-/
