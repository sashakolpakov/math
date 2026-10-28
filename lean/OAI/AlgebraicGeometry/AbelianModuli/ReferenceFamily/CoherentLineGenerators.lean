import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonGeneratedTwist
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence

/-! # Coherent Line Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentLineGenerators

noncomputable section

/-! Finite-type quasicoherent module sheaves on the original projective
variety have an epimorphic finite family of actual algebraic line bundles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance coherentLineGenerators_monoidal : MonoidalCategory V.carrier.Modules :=
  SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory V.carrier
attribute [local instance] MvPolynomial.gradedAlgebra

def HasFiniteLineGenerators (M : V.carrier.Modules) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
    (s : I → (L.sheaf ⟶ M)), Epi (Sigma.desc s)

theorem hasFiniteLineGenerators_of_generated_twist (M : V.carrier.Modules)
    (H : HilbertConstruction.Line.Bundles.LineBundle V.carrier) (h : SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators (M ⊗ H.sheaf)) :
    HasFiniteLineGenerators V M := by
  let hH := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible H
  let e := SheafCohomology.Projective.InvertibleTensorEquivalence.invertibleRightTensorEquivalence H.sheaf hH
  let G := e.inverse
  let D := RepresentationTheory.Theta.Geometric.AlgebraicHyperplaneBundle.lineBundleOfInvertible (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj H.sheaf) hH.dual
  let u : G.obj (HilbertConstruction.Line.Bundles.structureModule V.carrier) ≅ D.sheaf :=
    (tensorLeft (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj H.sheaf)).mapIso (SheafCohomology.Projective.TensorSections.monoidalUnitObjIso V.carrier).symm ≪≫
      ρ_ (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj H.sheaf)
  let a : G.obj (M ⊗ H.sheaf) ≅ M := (e.unitIso.app M).symm
  obtain ⟨I, hI, s, hs⟩ := h
  let : Fintype I := hI
  let : Epi (Sigma.desc s) := hs
  let t (i : I) := u.inv ≫ G.map (s i)
  let : Epi (Sigma.desc (fun i => G.map (s i))) :=
    SheafCohomology.Projective.EpiSectionFamily.epi_sigmaDesc_map G (fun _ : I => HilbertConstruction.Line.Bundles.structureModule V.carrier) s
  let : Epi (Sigma.desc t) := SheafCohomology.Projective.EpiSectionFamily.epi_sigmaDesc_precomp_iso
    (fun _ : I => D.sheaf) (fun _ : I => G.obj (HilbertConstruction.Line.Bundles.structureModule V.carrier))
    (fun _ => u.symm) (fun i => G.map (s i))
  exact ⟨I, hI, D, fun i => t i ≫ a.hom,
    SheafCohomology.Projective.EpiSectionFamily.epi_sigmaDesc_postcomp_iso (fun _ : I => D.sheaf) t a⟩

theorem coherent_hasFiniteLineGenerators (M : V.carrier.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : HasFiniteLineGenerators V M := by
  let f := V.presentation.projective.embedding
  let : IsClosedImmersion f := V.presentation.projective.closedImmersion
  obtain ⟨n, hn⟩ := SheafCohomology.Projective.ClosedGlobalGeneration.Dimension.closedProjective_eventually_hasFiniteGlobalGenerators
    (R := ℂ) (σ := Fin (V.ambientDimension + 1)) (X := V.carrier) f M 0
  let P := RepresentationTheory.Theta.Geometric.AlgebraicHyperplaneBundle.lineBundleOfInvertible
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := ℂ) (0 : Fin (V.ambientDimension + 1)) n)
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible 0 n)
  exact hasFiniteLineGenerators_of_generated_twist V M (P.pullback f) (hn n le_rfl)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoherentLineGenerators
