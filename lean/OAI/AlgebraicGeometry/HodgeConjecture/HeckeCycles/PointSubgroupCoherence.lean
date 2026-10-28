import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterPointCoherence
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

/-! # Point Subgroup Coherence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSubgroupCoherence.CM

noncomputable section

/-! Pullback and inverse image of actual point subgroups commute with
the canonical comparisons of scheme fiber products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

variable {S : Scheme} {g : ℕ} {A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem membership_iso (F : AbelianScheme.TateComparison.Subgroups.PointSubgroup A) {T U : Over S}
    (e : T ≅ U) (x : U ⟶ A.scheme) :
    e.hom ≫ x ∈ F.atTest T ↔ x ∈ F.atTest U := by
  constructor
  · intro hx
    have h := F.pullback_mem e.inv (e.hom ≫ x) hx
    simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp] using h
  · exact F.pullback_mem e.hom x

theorem comap_comp (F : AbelianScheme.TateComparison.Subgroups.PointSubgroup C) (f : A.scheme ⟶ B.scheme)
    (h : B.scheme ⟶ C.scheme) [IsMonHom f] [IsMonHom h] :
    (F.comapHom h).comapHom f = F.comapHom (f ≫ h) := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro T
  ext x
  change (x ≫ f) ≫ h ∈ F.atTest T ↔ x ≫ (f ≫ h) ∈ F.atTest T
  rw [Category.assoc]

theorem pullback_comap (F : AbelianScheme.TateComparison.Subgroups.PointSubgroup B) (f : A.scheme ⟶ B.scheme)
    [IsMonHom f] {T : Scheme} (b : T ⟶ S) :
    (F.comapHom f).pullback b =
      @AbelianScheme.TateComparison.Subgroups.PointSubgroup.comapHom T g (A.pullback b) (B.pullback b) (F.pullback b)
        ((Over.pullback b).map f)
        (inferInstanceAs (IsMonHom ((Over.pullback b).map f))) := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro U
  ext x
  change A.baseChangePointsEquiv b U x ≫ f ∈ F.atTest ((Over.map b).obj U) ↔
    B.baseChangePointsEquiv b U (x ≫ (Over.pullback b).map f) ∈ F.atTest ((Over.map b).obj U)
  rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map]

theorem pullback_factor (F : AbelianScheme.TateComparison.Subgroups.PointSubgroup A) {T U : Scheme}
    (f : U ⟶ T) (h : T ⟶ S) (x : U ⟶ S) (w : f ≫ h = x) :
    ((F.pullback h).pullback f).comapHom (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A f h x w).hom =
      F.pullback x := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro V
  ext z
  let c : Over.mk x ⟶ Over.mk h := Over.homMk f w
  have he := CMExtraction.IsogenyQuotient.ParameterPointCoherence.parameter_factor_original_point A c V z
  dsimp only [c] at he
  change A.baseChangePointsMulEquiv h ((Over.map f).obj V)
    ((A.pullback h).baseChangePointsMulEquiv f V
      (z ≫ (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A f h x w).hom)) ∈
      F.atTest ((Over.map h).obj ((Over.map f).obj V)) ↔
    A.baseChangePointsMulEquiv x V z ∈ F.atTest ((Over.map x).obj V)
  exact (iff_of_eq (congrArg (fun z => z ∈ F.atTest _) he)).trans
    (membership_iso F (AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso c V)
      (A.baseChangePointsMulEquiv x V z))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSubgroupCoherence.CM
