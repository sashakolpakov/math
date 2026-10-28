import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ZeroChartSheaf
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OverSubfunctor
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SubfunctorSchemeGluing
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctor

/-! # Product Zero Scheme -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! Glue actual normalized-frame charts to represent the zero fiber
of a rigidified product-family Picard map. All test schemes are retained. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (D : ProductLine.Construction.RigidifiedProductLine A B)

def ProductLine.Construction.RigidifiedProductLine.zeroSchemeSubfunctor : Subfunctor (yoneda.obj B.left) := OverSubfunctor.Construction.overSubfunctor D.zeroSubfunctor

omit [IsAlgClosed K] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem ProductLine.Construction.RigidifiedProductLine.zeroSchemeSubfunctor_isSheaf :
    Presieve.IsSheaf Scheme.zariskiTopology D.zeroSchemeSubfunctor.toFunctor :=
  Presieve.isSheaf_of_le _
    (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
      (OverSubfunctor.Construction.overSubfunctor_isSheaf D.zeroSubfunctor Scheme.fppfTopology D.zeroSubfunctor_isSheaf)

theorem ProductLine.Construction.RigidifiedProductLine.zeroChart_schemeFactorization {T : Over (Spec (.of K))}
    [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] (a : T ⟶ B)
    (Z : Scheme.{u}) (j : Z ⟶ T.left) :
    (j ≫ a.left) ∈ D.zeroSchemeSubfunctor.obj (op Z) ↔
      ∃ z : Z ⟶ (D.zeroChart a).left, z ≫ (D.zeroChart a).hom = j := by
  let U := Over.mk (j ≫ T.hom)
  let f : U ⟶ T := Over.homMk j rfl
  have hp := OverSubfunctor.Construction.overSubfunctor_mem D.zeroSubfunctor (f ≫ a)
  constructor
  · intro h
    obtain ⟨p⟩ := (D.zeroChart_hasLift_iff_relative_zero a f).mpr (hp.mp h)
    exact ⟨p.left, p.w⟩
  · rintro ⟨z, hz⟩
    exact hp.mpr ((D.zeroChart_hasLift_iff_relative_zero a f).mp ⟨Over.homMk z hz⟩)

variable [IsLocallyNoetherian B.left]

theorem ProductLine.Construction.RigidifiedProductLine.zeroSchemeSubfunctor_isRepresentable : D.zeroSchemeSubfunctor.toFunctor.IsRepresentable := by
  let U := B.left.affineCover
  let T := fun i : U.I₀ => Over.mk (U.f i ≫ B.hom)
  let a := fun i : U.I₀ => (Over.homMk (U.f i) rfl : T i ⟶ B)
  have : ∀ i, IsAffine (T i).left := fun i => inferInstanceAs (IsAffine (B.left.affineCover.X i))
  have : ∀ i, IsNoetherianRing Γ((T i).left, ⊤) := by
    intro i
    have : IsLocallyNoetherian (U.X i) := LocallyOfFiniteType.isLocallyNoetherian (U.f i)
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U.X i)⟩
  let M := fun i => D.zeroChart (a i)
  have : ∀ i, Mono (M i).hom := fun i => D.zeroChart_mono (a i)
  exact SubfunctorSchemeGluing.Construction.subfunctor_isRepresentable_of_openCover D.zeroSchemeSubfunctor U M
    (fun i Z j => D.zeroChart_schemeFactorization (a i) Z j) D.zeroSchemeSubfunctor_isSheaf

def ProductLine.Construction.RigidifiedProductLine.zeroScheme : Over B.left := by
  haveI := D.zeroSchemeSubfunctor_isRepresentable
  exact RepresentedSubfunctor.Construction.representedSubfunctorFamily D.zeroSchemeSubfunctor

instance ProductLine.Construction.RigidifiedProductLine.zeroScheme_mono : Mono D.zeroScheme.hom := by
  have := D.zeroSchemeSubfunctor_isRepresentable
  exact RepresentedSubfunctor.Construction.representedSubfunctorFamily_mono D.zeroSchemeSubfunctor

theorem ProductLine.Construction.RigidifiedProductLine.zeroScheme_hasLift_iff {T : Over (Spec (.of K))} (a : T ⟶ B) :
    Nonempty (Over.mk a.left ⟶ D.zeroScheme) ↔ D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  have := D.zeroSchemeSubfunctor_isRepresentable
  have hp := OverSubfunctor.Construction.overSubfunctor_mem D.zeroSubfunctor a
  have hf := RepresentedSubfunctor.Construction.representedSubfunctor_factorization D.zeroSchemeSubfunctor T.left a.left
  constructor
  · rintro ⟨v⟩
    exact hp.mp (hf.mpr ⟨v.left, v.w⟩)
  · intro h
    obtain ⟨v, hv⟩ := hf.mp (hp.mpr h)
    exact ⟨Over.homMk v hv⟩

def ProductLine.Construction.RigidifiedProductLine.zeroSchemeOver : Over (Spec (.of K)) := FamilyLiftFactorization.Construction.compositeFamily B D.zeroScheme

def ProductLine.Construction.RigidifiedProductLine.zeroInclusion : D.zeroSchemeOver ⟶ B := FamilyLiftFactorization.Construction.compositeFamilyMap B D.zeroScheme

theorem ProductLine.Construction.RigidifiedProductLine.zeroInclusion_factorization (T : Over (Spec (.of K))) (a : T ⟶ B) :
    D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T ↔ ∃ z : T ⟶ D.zeroSchemeOver, z ≫ D.zeroInclusion = a := by
  rw [← D.zeroScheme_hasLift_iff]
  constructor
  · rintro ⟨p⟩
    let z := FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv B D.zeroScheme a p
    exact ⟨z.val, z.property⟩
  · rintro ⟨z, hz⟩
    exact ⟨(FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv B D.zeroScheme a).symm ⟨z, hz⟩⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
