import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleEmbeddingPower
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveCohomologyFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

/-! # Proper Section Finiteness -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProperSectionFiniteness.Construction

noncomputable section

/-! Finite dimensionality of actual global sections on a proper scheme with an ample bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

universe u

def baseHZeroSectionsLinearEquiv {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) :
    letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M 0
    AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M 0 ≃ₗ[Γ(S, ⊤)] (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M := by
  letI := AlgebraicGeometry.SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule M 0
  letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M 0
  let e := AlgebraicGeometry.SheafCohomology.AffineH.Projective.hZeroCanonicalLinearEquivGlobalSections M
  exact { e.toAddEquiv with map_smul' := fun r x => e.map_smul (f.appTop r) x }

theorem closedProjective_globalSections_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} [X.IsSeparated]
    {r : ℕ} (a : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R))
    [IsClosedImmersion a] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(Spec (.of R), ⊤)
      ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj M) := by
  let f := a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ
  let U := fun j : ULift (Fin (r + 1)) => a ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) j
  have hU : IsOpenCover U :=
    (IsOpenCover.mk (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top
      (R := R) (σ := Fin (r + 1)))).comap a.base.hom
  have hUa (j : ULift (Fin (r + 1))) : IsAffineOpen (U j) :=
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage a
  let : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let : Module.Finite Γ(Spec (.of R), ⊤)
      ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U).homology 0) :=
    AlgebraicGeometry.SheafCohomology.Projective.TwistCechFinite.MvPolynomial.closedImmersion_finiteType_orderedBaseCechComplex_homology_module_finite a M 0
  let := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M 0
  let : Module.Finite Γ(Spec (.of R), ⊤) (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M 0) :=
    AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness.baseCohomologyFinite_of_orderedBaseCech f M U hU hUa 0
  exact Module.Finite.equiv (baseHZeroSectionsLinearEquiv f M)

theorem baseGlobalSections_finite_of_comp {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : S ⟶ T) (M : X.Modules)
    [Module.Finite Γ(T, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ g)).obj M)] :
    Module.Finite Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M) := by
  let e : (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (f ≫ g)).obj M →ₛₗ[g.appTop.hom]
      (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective e Function.surjective_id

theorem ample_proper_globalSections_finite
    {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [IsProper f]
    [IsNoetherianRing Γ(S, ⊤)] (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M) := by
  have : X.IsSeparated := ⟨(Limits.terminal.comp_from f) ▸
    (inferInstance : IsSeparated (f ≫ Limits.terminal.from S))⟩
  obtain ⟨d, hd, r, a, ha, hb, e⟩ := AmpleEmbeddingPower.Construction.ample_exists_closed_embedding_power f L hL
  have : IsClosedImmersion a := ha
  have ht := closedProjective_globalSections_finite a M
  rw [hb] at ht
  let := ht
  exact baseGlobalSections_finite_of_comp f S.toSpecΓ M

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProperSectionFiniteness.Construction
