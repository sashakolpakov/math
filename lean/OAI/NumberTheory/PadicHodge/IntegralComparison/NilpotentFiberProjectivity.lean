import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFiberAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointwiseGeometricProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.AmpleFiberPowerSections

/-! # Nilpotent Fiber Projectivity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFiberProjectivity.Ampleness

noncomputable section

/-! A proper flat family over a Noetherian affine nilpotent field
thickening is projective if its line bundle is ample on the reduction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.AmpleFiberPowerSections
universe u
variable {R k : Type u} [CommRing R] [CommRing k]
  (ρ : R →+* k) (hρ : Function.Surjective ρ)
  (hker : ∀ a ∈ RingHom.ker ρ, IsNilpotent a)
  {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of k))
  (i : Y ⟶ X) (hp : IsPullback i g f (Spec.map (CommRingCat.ofHom ρ)))
  (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : (L.pullback i).IsAmple)

variable [IsProper f] [Flat f] [IsNoetherianRing Γ(Spec (.of R), ⊤)]

include hρ hker hp hL in
def projectivePresentation : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f) :=
  L.projectivePresentation_of_geometric_fibers_of_pointwise_sections f
    (fun _K _ _ b => NilpotentFiberAmpleness.field_ample ρ hρ hker f g i hp L hL b)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.AmpleFiberPowerSections.properFlat_pointwise_power_sections_of_ample_fibers f L
      (fun x => NilpotentFiberAmpleness.field_ample ρ hρ hker f g i hp L hL ((Spec (.of R)).fromSpecResidueField x)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFiberProjectivity.Ampleness
