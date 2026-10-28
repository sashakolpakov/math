import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TorsionStabilizers
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter

/-! # Level Stabilizers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter

noncomputable section

/-! Full-level preservation on every scheme test is exactly principal
congruence on the actual native integral periods of the abelian scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Stabilizers.LevelCover OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TorsionStabilizers.IntrinsicLinearMaps

variable {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)

def nativeEndomorphism (f : A.scheme ⟶ A.scheme) :
    (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver ⟶ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver :=
  (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).inv

instance nativeEndomorphism_isMonHom (f : A.scheme ⟶ A.scheme) [IsMonHom f] :
    IsMonHom (nativeEndomorphism A P f) :=
  inferInstanceAs (IsMonHom ((Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).hom ≫ f ≫ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P).inv))

theorem nativeEndomorphism_comp (f h : A.scheme ⟶ A.scheme) :
    nativeEndomorphism A P (f ≫ h) = nativeEndomorphism A P f ≫ nativeEndomorphism A P h := by
  simp only [nativeEndomorphism, Category.assoc, Iso.inv_hom_id_assoc]

theorem nativeEndomorphism_id : nativeEndomorphism A P (𝟙 A.scheme) = 𝟙 _ := by
  simp only [nativeEndomorphism, Category.id_comp, Iso.hom_inv_id]

def nativeEndomorphismIso (e : A.scheme ≅ A.scheme) : (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver ≅ (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver where
  hom := nativeEndomorphism A P e.hom
  inv := nativeEndomorphism A P e.inv
  hom_inv_id := (nativeEndomorphism_comp A P e.hom e.inv).symm.trans
    ((congrArg (nativeEndomorphism A P) e.hom_inv_id).trans (nativeEndomorphism_id A P))
  inv_hom_id := (nativeEndomorphism_comp A P e.inv e.hom).symm.trans
    ((congrArg (nativeEndomorphism A P) e.inv_hom_id).trans (nativeEndomorphism_id A P))

theorem base_torsion_fix_iff_native (f : A.scheme ⟶ A.scheme) [IsMonHom f] :
    (∀ x : A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase), x.val ≫ f = x.val) ↔
      (∀ x : TorsionCongruence.TorusTorsion.killedBy (Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver)) N,
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (nativeEndomorphism A P f) x.val.toMul = x.val.toMul) := by
  let e := Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.nativeOverIso A P
  constructor
  · intro h x
    let y : A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) := ⟨x.val.toMul ≫ e.hom, by
      change (x.val.toMul ≫ e.hom) ^ N = 1
      rw [← MonObj.pow_comp, show x.val.toMul ^ N = 1 from x.property, MonObj.one_comp]⟩
    have hy := congrArg (fun q => q ≫ e.inv) (h y)
    change x.val.toMul ≫ (e.hom ≫ f ≫ e.inv) = x.val.toMul
    exact (Category.assoc _ _ _).symm.trans
      ((Category.assoc _ _ _).symm.trans
        (hy.trans ((Category.assoc _ _ _).trans
          ((congrArg (fun q => x.val.toMul ≫ q) e.hom_inv_id).trans (Category.comp_id _)))))
  · intro h x
    let y : TorsionCongruence.TorusTorsion.killedBy (Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P).toOver)) N :=
      ⟨Additive.ofMul (x.val ≫ e.inv), by
        change (x.val ≫ e.inv) ^ N = 1
        rw [← MonObj.pow_comp, show x.val ^ N = 1 from x.property, MonObj.one_comp]⟩
    have hy := congrArg (fun q => q ≫ e.hom) (h y)
    change ((x.val ≫ e.inv) ≫ (e.hom ≫ f ≫ e.inv)) ≫ e.hom =
      (x.val ≫ e.inv) ≫ e.hom at hy
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hy

/-- No choice of ordering changes the principal-congruence stabilizer:
the all-test full level is preserved exactly when the actual native
period lattice is fixed modulo N. -/
theorem preservesFullLevel_iff_native_congruence [NeZero N] (α : A.FullLevel N)
    (f : A.scheme ⟶ A.scheme) [IsMonHom f] :
    Level.Stabilizers.LevelCover.PreservesFullLevel α f ↔
      ∀ v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P), ∃ w ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P),
        Maps.IntrinsicLinearMaps.linearLift (nativeEndomorphism A P f) v - v = (N : ℤ) • w :=
  (Level.Stabilizers.LevelCover.preservesFullLevel_iff_base_torsion α f).trans
    ((base_torsion_fix_iff_native A P f).trans
      (TorsionStabilizers.IntrinsicLinearMaps.fixes_native_torsion_iff_congruence (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) N (nativeEndomorphism A P f)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LevelStabilizers.AbelianIntrinsicAdapter
