import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.TorsionHomRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.PointedMorphisms

/-! # Torsion Hom Cancellation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TorsionHomCancellation

noncomputable section

/-! Finite torsion on the target is enough to cancel a positive power of
homomorphisms from an abelian variety; no polarization on the target is
part of this cancellation lemma. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {K : Type u} [Field K] {g h : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))
variable (n : ℕ) [IsFinite (B.torsionScheme n).hom]

theorem abelian_torsion_hom_eq_one_of_finite (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (hf : f ^ n = 1) : f = 1 := by
  let t := (B.torsionSchemePointsEquiv n A.scheme).symm ⟨f, hf⟩
  have ht : t ≫ B.torsionInclusion n = f :=
    congrArg Subtype.val ((B.torsionSchemePointsEquiv n A.scheme).apply_symm_apply ⟨f, hf⟩)
  let : IsAffine (B.torsionScheme n).left := isAffine_of_isAffineHom (B.torsionScheme n).hom
  let : IsReduced A.scheme.left := A.reduced_overField
  let : ConnectedSpace A.scheme.left := A.connected_overField
  have he := Proper.ConnectedReducedConstants.properConnectedReduced_map_eq_constant A.scheme.hom t.left η[A.scheme].left η[A.scheme].w
  have hf' : f.left = A.scheme.hom ≫ η[A.scheme].left ≫ f.left := by
    have hh := congrArg (fun u => u ≫ (B.torsionInclusion n).left) he
    have ht' : t.left ≫ (B.torsionInclusion n).left = f.left := congrArg Over.Hom.left ht
    simpa only [Category.assoc, ht'] using hh
  have hz : η[A.scheme].left ≫ f.left = η[B.scheme].left :=
    congrArg Over.Hom.left (IsMonHom.one_hom f)
  apply Over.OverMorphism.ext
  exact hf'.trans (congrArg (fun u => A.scheme.hom ≫ u) hz)

theorem abelian_hom_pow_injective_of_finite_torsion
    (f k : A.scheme ⟶ B.scheme) [IsMonHom f] [IsMonHom k] (hfk : f ^ n = k ^ n) : f = k := by
  let : IsMonHom (f / k) := by
    apply Smooth.PointedMorphisms.abelianPointedMorphism_isMonHom A B
    have he : η[A.scheme] ≫ (f / k) = η[B.scheme] / η[B.scheme] :=
      (GrpObj.comp_div η[A.scheme] f k).trans
        (congrArg₂ (fun a b : 𝟙_ (Over (Spec (.of K))) ⟶ B.scheme => a / b)
          (IsMonHom.one_hom f) (IsMonHom.one_hom k))
    have hη : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ B.scheme) = η[B.scheme] := by
      simp only [MonObj.one_eq_one]
    exact he.trans ((div_self' η[B.scheme]).trans hη)
  have hdiv : (f / k) ^ n = 1 := (div_pow f k n).trans
    ((congrArg (fun z : A.scheme ⟶ B.scheme => z / k ^ n) hfk).trans (div_self' (k ^ n)))
  exact div_eq_one.mp (abelian_torsion_hom_eq_one_of_finite A B n (f / k) hdiv)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TorsionHomCancellation
