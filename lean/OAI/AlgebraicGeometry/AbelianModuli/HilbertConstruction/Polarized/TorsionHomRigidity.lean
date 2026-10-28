import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.MultiplicationFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support

/-! # Torsion Hom Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.TorsionHomRigidity

noncomputable section

/-! A group homomorphism from an abelian variety to a polarized abelian variety has no nonzero integer torsion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g h N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (B : Abelian.Schemes.AbelianScheme h (Spec (.of K)))

theorem polarized_torsion_hom_eq_one (f : B.scheme ⟶ A.abelian.scheme) [IsMonHom f]
    (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) : f = 1 := by
  let t := (A.abelian.torsionSchemePointsEquiv n B.scheme).symm ⟨f, hf⟩
  have ht : t ≫ A.abelian.torsionInclusion n = f :=
    congrArg Subtype.val ((A.abelian.torsionSchemePointsEquiv n B.scheme).apply_symm_apply ⟨f, hf⟩)
  have : IsFinite (A.abelian.torsionScheme n).hom := A.torsionScheme_isFinite_overBase n hn
  have : IsAffine (A.abelian.torsionScheme n).left := isAffine_of_isAffineHom (A.abelian.torsionScheme n).hom
  have : IsReduced B.scheme.left := B.reduced_overField
  have : ConnectedSpace B.scheme.left := B.connected_overField
  have he := Proper.ConnectedReducedConstants.properConnectedReduced_map_eq_constant B.scheme.hom t.left η[B.scheme].left η[B.scheme].w
  have hf' : f.left = B.scheme.hom ≫ η[B.scheme].left ≫ f.left := by
    have h := congrArg (fun u => u ≫ (A.abelian.torsionInclusion n).left) he
    have ht' : t.left ≫ (A.abelian.torsionInclusion n).left = f.left := congrArg Over.Hom.left ht
    simpa only [Category.assoc, ht'] using h
  have hz : η[B.scheme].left ≫ f.left = η[A.abelian.scheme].left :=
    congrArg Over.Hom.left (IsMonHom.one_hom f)
  apply Over.OverMorphism.ext
  exact hf'.trans (congrArg (fun u => B.scheme.hom ≫ u) hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.TorsionHomRigidity
