import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroSheaf
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverSubfunctor
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorSchemeGluing
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctor

/-! # Relative Zero Scheme -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! Actual normalized-frame charts glue to the zero scheme of the
original relative Picard map of a varying projective group family.
The representing property is on all schemes over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme} {A B : Over S} [GrpObj A]
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

def zeroSchemeSubfunctor : Subfunctor (yoneda.obj B.left) := FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor (RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts.zeroSubfunctor D)

theorem zeroSchemeSubfunctor_isSheaf :
    Presieve.IsSheaf Scheme.zariskiTopology (zeroSchemeSubfunctor D).toFunctor :=
  Presieve.isSheaf_of_le _
    (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
      (FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor_isSheaf (RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts.zeroSubfunctor D) Scheme.fppfTopology (RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts.zeroSubfunctor_isSheaf D))

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A)

theorem zeroChart_schemeFactorization {T : Over S}
    [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [IsLocallyNoetherian T.left]
    (a : T ⟶ B) (Z : Scheme) (j : Z ⟶ T.left) :
    (j ≫ a.left) ∈ (zeroSchemeSubfunctor D).obj (op Z) ↔
      ∃ z : Z ⟶ (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D a).left, z ≫ (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D a).hom = j := by
  let U := Over.mk (j ≫ T.hom)
  let f : U ⟶ T := Over.homMk j rfl
  have hp := FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor_mem (RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts.zeroSubfunctor D) (f ≫ a)
  constructor
  · intro h
    obtain ⟨p⟩ := (RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts.zeroChart_hasLift_iff_relative_zero D P a f).mpr (hp.mp h)
    exact ⟨p.left, p.w⟩
  · rintro ⟨z, hz⟩
    exact hp.mpr ((RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts.zeroChart_hasLift_iff_relative_zero D P a f).mp ⟨Over.homMk z hz⟩)

variable [IsLocallyNoetherian B.left]

include P in
theorem zeroSchemeSubfunctor_isRepresentable : (zeroSchemeSubfunctor D).toFunctor.IsRepresentable := by
  let U := B.left.affineCover
  let T := fun i : U.I₀ => Over.mk (U.f i ≫ B.hom)
  let a := fun i : U.I₀ => (Over.homMk (U.f i) rfl : T i ⟶ B)
  let (i : U.I₀) : IsAffine (T i).left := inferInstanceAs (IsAffine (B.left.affineCover.X i))
  let (i : U.I₀) : IsLocallyNoetherian (T i).left :=
    LocallyOfFiniteType.isLocallyNoetherian (U.f i)
  let (i : U.I₀) : IsNoetherianRing Γ((T i).left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U.X i)⟩
  let M := fun i => RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D (a i)
  let (i : U.I₀) : Mono (M i).hom := RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart_mono P D (a i)
  exact FormalGeometry.Completion.SubfunctorSchemeGluing.Construction.subfunctor_isRepresentable_of_openCover (zeroSchemeSubfunctor D) U M
    (fun i Z j => zeroChart_schemeFactorization D P (a i) Z j) (zeroSchemeSubfunctor_isSheaf D)

def zeroScheme : Over B.left := by
  letI := zeroSchemeSubfunctor_isRepresentable D P
  exact FormalGeometry.Completion.RepresentedSubfunctor.Construction.representedSubfunctorFamily (zeroSchemeSubfunctor D)

instance zeroScheme_mono : Mono (zeroScheme D P).hom := by
  let := zeroSchemeSubfunctor_isRepresentable D P
  exact FormalGeometry.Completion.RepresentedSubfunctor.Construction.representedSubfunctorFamily_mono (zeroSchemeSubfunctor D)

theorem zeroScheme_hasLift_iff {T : Over S} (a : T ⟶ B) :
    Nonempty (Over.mk a.left ⟶ zeroScheme D P) ↔
      D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  let := zeroSchemeSubfunctor_isRepresentable D P
  have hp := FormalGeometry.Completion.OverSubfunctor.Construction.overSubfunctor_mem (RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts.zeroSubfunctor D) a
  have hf := FormalGeometry.Completion.RepresentedSubfunctor.Construction.representedSubfunctor_factorization (zeroSchemeSubfunctor D) T.left a.left
  constructor
  · rintro ⟨v⟩
    exact hp.mp (hf.mpr ⟨v.left, v.w⟩)
  · intro h
    obtain ⟨v, hv⟩ := hf.mp (hp.mpr h)
    exact ⟨Over.homMk v hv⟩

def zeroSchemeOver : Over S := FormalGeometry.Completion.FamilyLiftFactorization.Construction.compositeFamily B (zeroScheme D P)

def zeroInclusion : zeroSchemeOver D P ⟶ B := FormalGeometry.Completion.FamilyLiftFactorization.Construction.compositeFamilyMap B (zeroScheme D P)

theorem zeroInclusion_factorization (T : Over S) (a : T ⟶ B) :
    D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T ↔
      ∃ z : T ⟶ zeroSchemeOver D P, z ≫ zeroInclusion D P = a := by
  rw [← zeroScheme_hasLift_iff D P a]
  constructor
  · rintro ⟨p⟩
    let z := FormalGeometry.Completion.FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv B (zeroScheme D P) a p
    exact ⟨z.val, z.property⟩
  · rintro ⟨z, hz⟩
    exact ⟨(FormalGeometry.Completion.FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv B (zeroScheme D P) a).symm ⟨z, hz⟩⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroScheme.Geometric.RelativeRigidifiedCharts
