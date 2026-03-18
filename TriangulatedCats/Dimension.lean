import Mathlib.CategoryTheory.Triangulated.Subcategory

/-
  Define basic definitions for Rouquier dimension, including:
  · add(I)
  · smd(I)
  · I ⋆ J
  · ⟨G⟩_k
-/

section basic

open CategoryTheory
open Limits Category Preadditive Pretriangulated ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C] [HasCoproducts C]

inductive addc (I : Set C) : Set C
| of_mem' {a : C} : I a → addc I a
| of_shift' {i : ℤ} {a : C} : addc I a → addc I (a⟦i⟧)
| of_iso' {a b : C} : addc I a → Nonempty (a ≅ b) → addc I b
| biprod' {a b : C} : addc I a → addc I b → addc I (a ⊞ b)

inductive smd (I : Set C) : Set C
| of_mem' {a : C} : I a → smd I a
| of_smd_left' {a b : C} : smd I (a ⊞ b) → smd I a
| of_smd_right' {a b : C} : smd I (a ⊞ b) → smd I b

def star' (I J : Set C) : Set C :=
  {c | ∃ a ∈ I, ∃ b ∈ J, ∃ f : a ⟶ c, ∃ g : c ⟶ b, ∃ h : b ⟶ a⟦1⟧, Triangle.mk f g h ∈ distTriang C}

infixl:60 " ⋆ " => star'

def star_assoc [IsTriangulated C] (I J K : Set C) : I ⋆ J ⋆ K = I ⋆ (J ⋆ K) := by
  ext c
  constructor
  . rintro ⟨b₁, ⟨a₁, ha₁, a₂, ha₂, f', g', h', H'⟩, b₂, hb₂, f, g, h, H⟩
    obtain ⟨c₂, f'', g'', H''⟩ := distinguished_cocone_triangle (f' ≫ f)
    obtain ⟨O⟩ := IsTriangulated.octahedron_axiom (rfl) H' H H''
    refine ⟨a₁, ha₁, c₂, ⟨a₂, ha₂, b₂, hb₂, _, _, _, O.mem⟩, _, _, _, H''⟩
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

def dia (I J : Set C) : Set C := smd (star' I J)

def level (I : Set C) : ℕ → Set C
| 0 => smd (addc {0})
| (n + 1) => dia (level I n) I

def thick_cl (I : Set C) : Set C := ⋃ n : ℕ, level I n

def is_generator (G : C) := thick_cl {G} = ⊤

def addc_monotone : Monotone (addc (C := C)) := by
  intro I J hIJ a ha
  induction ha with
  | of_mem' ha => exact addc.of_mem' (hIJ ha)
  | of_shift' ha ih => exact addc.of_shift' ih
  | of_iso' ha hab ih => exact addc.of_iso' ih hab
  | biprod' _ _ iha ihb => exact addc.biprod' iha ihb

def smd_monotone : Monotone (smd (C := C)) := by
  intro I J hIJ a ha
  induction ha with
  | of_mem' ha => exact smd.of_mem' (hIJ ha)
  | of_smd_left' _ ih => exact smd.of_smd_left' ih
  | of_smd_right' _ ih => exact smd.of_smd_right' ih

end basic
