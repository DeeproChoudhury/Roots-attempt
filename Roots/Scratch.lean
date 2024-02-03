import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.QuadraticForm.Basic

noncomputable section

open scoped TensorProduct BigOperators Classical Pointwise

open Set Function

variable {k V : Type _} [CommRing k] [AddCommGroup V] [Module k V]

theorem Unit.apply_root_mem {Φ : Set V} (u : MulAction.stabilizer (V ≃ₗ[k] V) Φ) (x : Φ) :
    u.val (x : V) ∈ Φ := by
  obtain ⟨u, hu⟩ := u
  obtain ⟨x, hx⟩ := x
  change u x ∈ Φ
  rw [MulAction.mem_stabilizer_iff] at hu
  replace hu : u '' Φ = Φ := by rwa [← image_smul] at hu
  rw [← hu]
  exact mem_image_of_mem u hx

@[simps]
def Unit.toPerm {Φ : Set V} (u : MulAction.stabilizer (V ≃ₗ[k] V) Φ) : Equiv.Perm Φ
    where
  toFun x := ⟨u.val x, Unit.apply_root_mem u x⟩
  invFun x := ⟨u.val⁻¹ x, Unit.apply_root_mem u⁻¹ x⟩
  left_inv := by
    intro x
    simp only [Subtype.coe_mk]
    apply Subtype.eq
    simp
    exact (u : V ≃ₗ[k] V).symm_apply_apply x
  right_inv := by
    intro x
    simp only [Subtype.coe_mk]
    ext
    simp
    exact (u : V ≃ₗ[k] V).apply_symm_apply x

@[simps]
def Unit.toPerm' {Φ : Set V} : MulAction.stabilizer (V ≃ₗ[k] V) Φ →* Equiv.Perm Φ
    where
  toFun := Unit.toPerm
  map_one' := by
    ext
    simp
  map_mul' := by
    intro u₁ u₂
    ext
    simp
    rfl

theorem Unit.injective_toPerm' {Φ : Set V} (hΦ : Submodule.span k Φ = ⊤) :
    Injective (Unit.toPerm' : MulAction.stabilizer (V ≃ₗ[k] V) Φ → Equiv.Perm Φ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  rw [MonoidHom.mem_ker] at hu
  have hu' := DFunLike.congr_fun hu
  change ∀ x, _ = x at hu'
  ext v
  change u.val v = v
  have := DFunLike.congr_fun hu
  simp only [Unit.toPerm'_apply, Equiv.Perm.coe_one, id.def, SetCoe.forall] at this
  have mem1 : v ∈ Submodule.span k Φ := by
    rw [hΦ]
    exact Submodule.mem_top
  refine Submodule.span_induction mem1 ?_ ?_ ?_ ?_
  · intro x hx
    specialize hu'
    dsimp at hu'
    simp at hu'
    exact hu'
  · exact LinearEquiv.map_zero _
  · intro x y hx hy
    erw [LinearEquiv.map_add]
    change u.val x + u.val y = x + y
    rw [hx, hy]
  · intro t x hx
    erw [LinearEquiv.map_smul]
    change t • u.val x = t • x
    rw [hx]
