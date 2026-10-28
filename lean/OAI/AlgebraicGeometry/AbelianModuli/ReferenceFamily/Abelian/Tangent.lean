import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentBasePoint
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.DualObstructionCriterion

/-! # Tangent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.Tangent

noncomputable section

/-! The actual tangent and fixed fibers of a proper smooth connected
commutative group family retain their required geometric properties. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (R : Type) [CommRing R] [Algebra R ℂ] (X : Over (Spec (.of R)))

attribute [local implicit_reducible] TangentBasePoint.tangentFamily TangentBasePoint.fixedFamilyFiber

theorem abelianFamilyFixedFiber_smooth [Smooth X.hom] : Smooth (TangentBasePoint.fixedFamilyFiber ℂ R X).hom :=
  inferInstanceAs (Smooth (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))))

theorem abelianFamilyFixedFiber_proper [IsProper X.hom] : IsProper (TangentBasePoint.fixedFamilyFiber ℂ R X).hom :=
  inferInstanceAs (IsProper (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))))

theorem abelianFamilyFixedFiber_connected [GeometricallyConnected X.hom] : GeometricallyConnected (TangentBasePoint.fixedFamilyFiber ℂ R X).hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))))

attribute [local instance] abelianFamilyFixedFiber_smooth abelianFamilyFixedFiber_proper abelianFamilyFixedFiber_connected

theorem abelianFamilyFixedFiber_integral [GrpObj X] [IsCommMonObj X]
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom] : IsIntegral (TangentBasePoint.fixedFamilyFiber ℂ R X).left := by
  have : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom :=
    abelianFamilyFixedFiber_smooth R X
  have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom :=
    abelianFamilyFixedFiber_proper R X
  have : GeometricallyConnected ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom :=
    abelianFamilyFixedFiber_connected R X
  exact Picard.Homomorphisms.GroupRigidity.Construction.integral_smooth_proper_connected_group
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X)

variable [Algebra ℂ R] [IsScalarTower ℂ R ℂ]

theorem abelianFamilyTangent_smooth [Smooth X.hom] (d : Derivation ℂ R ℂ) : Smooth (TangentBasePoint.tangentFamily ℂ R X d).hom :=
  inferInstanceAs (Smooth (pullback.snd X.hom (TangentBasePoint.tangentBasePoint ℂ R d)))

theorem abelianFamilyTangent_proper [IsProper X.hom] (d : Derivation ℂ R ℂ) : IsProper (TangentBasePoint.tangentFamily ℂ R X d).hom :=
  inferInstanceAs (IsProper (pullback.snd X.hom (TangentBasePoint.tangentBasePoint ℂ R d)))

theorem abelianFamilyTangent_connected [GeometricallyConnected X.hom] (d : Derivation ℂ R ℂ) :
    GeometricallyConnected (TangentBasePoint.tangentFamily ℂ R X d).hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd X.hom (TangentBasePoint.tangentBasePoint ℂ R d)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.Tangent
