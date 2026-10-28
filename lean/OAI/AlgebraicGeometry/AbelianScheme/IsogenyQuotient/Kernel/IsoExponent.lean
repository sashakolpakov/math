import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TypeTransport

/-! # Iso Exponent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.IsoExponent.Construction

noncomputable section

/-! Actual kernel group-scheme isomorphisms transport exponent bounds
on all scheme-valued points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TypeTransport
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

universe u
variable {S : Scheme.{u}} {A B Z W : Over S}
  [GrpObj A] [GrpObj B] [GrpObj Z] [GrpObj W]
  (φ : A ⟶ Z) [IsMonHom φ] (q : B ⟶ W) [IsMonHom q]
  (e : Picard.PoincareBundle.Kernel.Scheme.kernelObject φ ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject q) [IsMonHom e.hom]

include e in
theorem kernelIso_transports_exponent (d : ℕ)
    (hφ : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
    (T : Over S) (x : T ⟶ B) (hx : x ≫ q = 1) : x ^ d = 1 := by
  let y := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv q T).symm ⟨x, hx⟩
  let z := (Picard.PoincareBundle.Kernel.TypeTransport.representedPointsMulEquiv e T).symm y
  have hz : z ^ d = 1 := by
    apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion φ)).mp
    rw [MonObj.pow_comp, MonObj.one_comp]
    apply hφ T (z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion φ)
    rw [Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]
  have hy : y ^ d = 1 := by
    have h := congrArg (Picard.PoincareBundle.Kernel.TypeTransport.representedPointsMulEquiv e T) hz
    rw [map_pow, map_one, MulEquiv.apply_symm_apply] at h
    exact h
  have h := congrArg (Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv q T) hy
  rw [map_pow, map_one, MulEquiv.apply_symm_apply] at h
  exact congrArg Subtype.val h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.IsoExponent.Construction
