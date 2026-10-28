import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The geometric isomorphism specified by a full level structure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g N : ℕ} {S : Scheme.{u}}

/-- A constant scheme is etale over its base. -/
instance Level.Scheme.constantScheme_etale (S : Scheme.{u}) (I : Type u) :
    Etale (ConstantScheme.Iff.constantScheme S I).hom := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @Etale.{u}) (Q := @RingHom.Etale)
  change Etale (Sigma.desc (fun _ : I => 𝟙 S))
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u})
    (fun _ => inferInstanceAs (Etale (𝟙 S)))

/-- A constant scheme is locally quasi-finite over its base. -/
instance Level.Scheme.constantScheme_locallyQuasiFinite (S : Scheme.{u}) (I : Type u) :
    LocallyQuasiFinite (ConstantScheme.Iff.constantScheme S I).hom := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @LocallyQuasiFinite.{u}) (Q := @RingHom.QuasiFinite)
  change LocallyQuasiFinite (Sigma.desc (fun _ : I => 𝟙 S))
  exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyQuasiFinite.{u})
    (fun _ => inferInstanceAs (LocallyQuasiFinite (𝟙 S)))

/-- The split scheme with labels in the ordered standard level module. -/
def Level.Scheme.constantFullLevelScheme (g N : ℕ) (S : Scheme.{u}) : Over S :=
  ConstantScheme.Iff.constantScheme S (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)))

/-- The split scheme represents the constant ordered-level functor. -/
def Level.Scheme.constantFullLevelRepresentable (g N : ℕ) (S : Scheme.{u}) :
    (Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⋙ forget GrpCat).RepresentableBy
      (Level.Scheme.constantFullLevelScheme g N S) where
  homEquiv {T} := (ConstantScheme.Iff.constantSchemePointsEquiv S _ T).trans (LocallyConstant.congrRight Equiv.ulift)
  homEquiv_comp h t := by
    apply LocallyConstant.ext
    intro x
    rfl

variable {A : Abelian.Schemes.AbelianScheme g S}

/-- A full level structure identifies the split scheme with the actual torsion scheme. -/
def Abelian.Schemes.AbelianScheme.FullLevel.schemeIso (level : A.FullLevel N) : Level.Scheme.constantFullLevelScheme g N S ≅ A.torsionScheme N :=
  ((Level.Scheme.constantFullLevelRepresentable g N S).ofIso
    (Functor.isoWhiskerRight level (forget GrpCat))).uniqueUpToIso (A.torsionRepresentable N)

/-- The geometric trivialization sends the universal ordered labels to the chosen basis. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.schemeIso_hom_basis (level : A.FullLevel N) :
    level.schemeIso.hom ≫ A.torsionInclusion N =
      (level.hom.app (.op (Level.Scheme.constantFullLevelScheme g N S))
        ((Level.Scheme.constantFullLevelRepresentable g N S).homEquiv (𝟙 _))).val :=
  congrArg (fun x : A.torsionPoints N (Level.Scheme.constantFullLevelScheme g N S) => x.val)
    ((A.torsionSchemePointsEquiv N (Level.Scheme.constantFullLevelScheme g N S)).apply_symm_apply _)

/-- A full level structure implies that the torsion scheme is etale over the base. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.torsion_etale (level : A.FullLevel N) : Etale (A.torsionScheme N).hom := by
  have : IsIso level.schemeIso.inv.left :=
    inferInstanceAs (IsIso (((Over.forget S).mapIso level.schemeIso).inv))
  have : Etale (Level.Scheme.constantFullLevelScheme g N S).hom :=
    Level.Scheme.constantScheme_etale S _
  rw [← level.schemeIso.inv.w]
  infer_instance

/-- A full level structure implies that the torsion scheme is locally quasi-finite. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.torsion_locallyQuasiFinite (level : A.FullLevel N) :
    LocallyQuasiFinite (A.torsionScheme N).hom := by
  have : IsIso level.schemeIso.inv.left :=
    inferInstanceAs (IsIso (((Over.forget S).mapIso level.schemeIso).inv))
  have : LocallyQuasiFinite (Level.Scheme.constantFullLevelScheme g N S).hom :=
    Level.Scheme.constantScheme_locallyQuasiFinite S _
  rw [← level.schemeIso.inv.w]
  infer_instance

/-- The torsion scheme of a full-level abelian scheme is finite over the base. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.torsion_finite (level : A.FullLevel N) : IsFinite (A.torsionScheme N).hom := by
  have := level.torsion_locallyQuasiFinite
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
