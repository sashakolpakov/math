import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Compact
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteTestEmbedding
import OAI.RepresentationTheory.Weil.Local.LinearSubstitution

/-! # Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Action

noncomputable section

/-! Restrict the actual finite SL3 coset sum to radial inputs. Closure
is proved using integral orbits, compact support, and local constancy. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.FiniteTestEmbedding.Realization

variable (q : ℕ) [Fact q.Prime]

def compactFunctions : Submodule ℂ (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.comp (fun z : ℂ => c * z), hf.2.smul_left⟩

theorem matrixSubstitution_compact (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) (f : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q → ℂ)
    (hf : f ∈ compactFunctions q) : Hecke.matrixSubstitution q g f ∈ compactFunctions q := by
  let e := RepresentationTheory.Weil.Local.LinearSubstitution.Construction.positionAddEquiv (Matrix.SpecialLinearGroup.toGL g)⁻¹
  change IsLocallyConstant (f ∘ e) ∧ HasCompactSupport (f ∘ e)
  exact ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e.toHomeomorph⟩

theorem sphericalFunctionAction_compact (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    Hecke.sphericalFunctionAction q T b.val ∈ compactFunctions q := by
  change (((RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.kernel (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T).sum fun c a =>
    (a : ℂ) • (Hecke.matrixSubstitution q c.out).toLinearMap) b.val) ∈ compactFunctions q
  rw [LinearMap.finsupp_sum_apply]
  apply Submodule.sum_mem
  intro c _
  exact (compactFunctions q).smul_mem _
    (matrixSubstitution_compact q c.out b.val (RepresentationTheory.Hecke.RadialDilation.FiniteTestEmbedding.Realization.radial_regular q b))

theorem sphericalFunctionAction_radial (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    Hecke.sphericalFunctionAction q T b.val ∈ RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q := by
  have h := sphericalFunctionAction_compact q T b
  exact Compact.integral_fixed_compact_mem q
    ⟨_, Hecke.spherical_radial_integral_fixed q T b⟩ h.1 h.2

def sphericalRadialAction (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q :=
  LinearMap.codRestrict (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)
    ((Hecke.sphericalFunctionAction q T).comp (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q).subtype)
    (sphericalFunctionAction_radial q T)

theorem sphericalRadialAction_apply (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    (sphericalRadialAction q T b).val = Hecke.sphericalFunctionAction q T b.val := rfl

theorem sphericalRadialAction_dilation (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    sphericalRadialAction q T (Cyclicity.dilationEquiv q b) =
      Cyclicity.dilationEquiv q (sphericalRadialAction q T b) := by
  apply Subtype.ext
  exact Hecke.sphericalFunctionAction_dilation q T b.val

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Action
