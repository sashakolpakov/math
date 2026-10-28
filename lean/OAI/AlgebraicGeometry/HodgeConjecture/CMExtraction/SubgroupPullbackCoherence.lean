import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroup
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterPointCoherence
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELCoherence

/-! # Subgroup Pullback Coherence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SubgroupPullbackCoherence.IsogenyQuotient

noncomputable section

section

/-! Exact subgroup-functor coherence for pullback and group-isomorphism
transport. Every equality is proved by membership on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme} {g : ℕ} {A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem subgroup_membership_iso (H : AbelianScheme.TateComparison.Subgroups.PointSubgroup A) {V W : Over S}
    (e : V ≅ W) (x : W ⟶ A.scheme) : e.hom ≫ x ∈ H.atTest V ↔ x ∈ H.atTest W := by
  constructor
  · intro hx
    have hh := H.pullback_mem e.inv (e.hom ≫ x) hx
    simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hh
  · exact H.pullback_mem e.hom x

theorem subgroup_comap_comp (H : AbelianScheme.TateComparison.Subgroups.PointSubgroup C)
    (f : B.scheme ⟶ C.scheme) [IsMonHom f] (h : A.scheme ⟶ B.scheme) [IsMonHom h] :
    (H.comapHom f).comapHom h = H.comapHom (h ≫ f) := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro V
  ext x
  change (x ≫ h) ≫ f ∈ H.atTest V ↔ x ≫ (h ≫ f) ∈ H.atTest V
  rw [Category.assoc]

theorem subgroup_comap_iso_inverse (H : AbelianScheme.TateComparison.Subgroups.PointSubgroup A) (e : A.scheme ≅ B.scheme)
    [IsMonHom e.hom] [IsMonHom e.inv] :
    (H.comapHom e.inv).comapHom e.hom = H := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro V
  ext x
  change (x ≫ e.hom) ≫ e.inv ∈ H.atTest V ↔ x ∈ H.atTest V
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem subgroup_pullback_comap (H : AbelianScheme.TateComparison.Subgroups.PointSubgroup B) (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (b : T ⟶ S) :
    (H.comapHom f).pullback b = @AbelianScheme.TateComparison.Subgroups.PointSubgroup.comapHom T g (A.pullback b)
      (B.pullback b) (H.pullback b) ((Over.pullback b).map f)
        (inferInstanceAs (IsMonHom ((Over.pullback b).map f))) := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro V
  ext x
  change A.baseChangePointsMulEquiv b V x ≫ f ∈ H.atTest ((Over.map b).obj V) ↔
    B.baseChangePointsMulEquiv b V (x ≫ (Over.pullback b).map f) ∈ H.atTest ((Over.map b).obj V)
  exact iff_of_eq (congrArg (fun y => y ∈ H.atTest ((Over.map b).obj V))
    (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f b V x)).symm

end

/-! Composition of actual subgroup pullbacks, with the canonical PEL
comparison maps and membership on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T V : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (H : AbelianScheme.TateComparison.Subgroups.PointSubgroup A) (r : V ⟶ T) (s : T ⟶ S)

theorem subgroup_pullback_factor :
    ((H.pullback s).pullback r).comapHom (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A r s (r ≫ s) rfl).hom =
      H.pullback (r ≫ s) := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro U
  ext z
  change A.baseChangePointsMulEquiv s ((Over.map r).obj U)
      ((A.pullback s).baseChangePointsMulEquiv r U
        (z ≫ (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso A r s (r ≫ s) rfl).hom)) ∈
          H.atTest ((Over.map s).obj ((Over.map r).obj U)) ↔
    A.baseChangePointsMulEquiv (r ≫ s) U z ∈ H.atTest ((Over.map (r ≫ s)).obj U)
  have hp := IsogenyQuotient.ParameterPointCoherence.parameter_factor_original_point A
    (P := Over.mk (r ≫ s)) (Q := Over.mk s) (Over.homMk r rfl) U z
  exact (iff_of_eq (congrArg (fun y =>
    y ∈ H.atTest ((Over.map s).obj ((Over.map r).obj U))) hp)).trans
      (subgroup_membership_iso H
        (AbelianScheme.CartierDuality.ParameterKernelPoints.Construction.KernelCharacters.parameterTestIso (P := Over.mk (r ≫ s))
          (Q := Over.mk s) (Over.homMk r rfl) U)
        (A.baseChangePointsMulEquiv (r ≫ s) U z))

theorem subgroup_comap_congr {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (G : AbelianScheme.TateComparison.Subgroups.PointSubgroup B)
    (f h : A.scheme ⟶ B.scheme) [IsMonHom f] [IsMonHom h] (w : f = h) :
    G.comapHom f = G.comapHom h := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro U
  ext z
  change z ≫ f ∈ G.atTest U ↔ z ≫ h ∈ G.atTest U
  rw [w]

theorem subgroup_pullback_comp {R : Type} [CommRing R] {N : ℕ}
    (F : AbelianScheme.TateComparison.PEL.PELFamilyData R g N S) (G : AbelianScheme.TateComparison.Subgroups.PointSubgroup F.abelian) :
    (G.pullback (r ≫ s)).comapHom (F.pullbackComp s r).abelian.hom =
      (G.pullback s).pullback r := by
  have hf := subgroup_pullback_factor F.abelian G r s
  have he := F.pullbackFactor_abelian r s (r ≫ s) rfl
  have hh : (F.pullbackComp s r).abelian.inv =
      (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso F.abelian r s (r ≫ s) rfl).hom :=
    congrArg (fun e => e.hom) he
  have hg := (subgroup_comap_congr _ ((G.pullback s).pullback r) _ _ hh).trans hf
  rw [← hg]
  exact subgroup_comap_iso_inverse _ (F.pullbackComp s r).abelian

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SubgroupPullbackCoherence.IsogenyQuotient
