import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels

/-! # Compact Kernels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactKernels.Construction

noncomputable section

/-!
The ordinary multiplicative prescription is the whole compact block in
the pure multiplicative case and the identity subgroup in the pure etale
case. The identity subgroup is tested on every scheme, not confused with
the empty scheme subobject.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable (R : Type u) [CommRing R] (q n : ℕ)

instance etaleZero_points (T : Over (Spec (.of R))) :
    Subsingleton (T ⟶ (OrdinaryBlocks.Construction.etaleOrdinaryBlock R q n 0).X) := by
  let e : (T ⟶ (OrdinaryBlocks.Construction.etaleOrdinaryBlock R q n 0).X) ≃*
      LocallyConstant T.left (OrdinaryBlocks.Construction.OrdinaryBlockLabels q n 0) :=
    ((EtaleSubgroups.Construction.etaleGroupPointIso (Spec (.of R)) (OrdinaryBlocks.Construction.OrdinaryBlockLabels q n 0)).app (.op T)).groupIsoToMulEquiv
  constructor
  intro a b
  apply e.injective
  apply LocallyConstant.ext
  intro t
  exact Subsingleton.elim _ _

instance multiplicativeZero_structural_isIso : IsIso (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock R q n 0).X.hom := by
  let A := MonoidAlgebra R (OrdinaryBlocks.Construction.OrdinaryBlockLabels.{u} q n 0)
  let e : A ≃ₐ[R] R := MonoidAlgebra.uniqueAlgEquiv R (OrdinaryBlocks.Construction.OrdinaryBlockLabels q n 0)
  have he : CommRingCat.ofHom (algebraMap R A) = e.symm.toRingEquiv.toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change (algebraMap R A) r = e.symm r
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using (e.symm.commutes r).symm
  have : IsIso (CommRingCat.ofHom (algebraMap R A)) := by rw [he]; infer_instance
  change IsIso (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  infer_instance

instance multiplicativeZero_points (T : Over (Spec (.of R))) :
    Subsingleton (T ⟶ (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock R q n 0).X) := by
  constructor
  intro a b
  apply Over.OverMorphism.ext
  apply (cancel_mono (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock R q n 0).X.hom).mp
  exact a.w.trans b.w.symm

/-- In a pure multiplicative compact block, the chosen inclusion is an
isomorphism onto the whole block, at every torsion level. -/
instance ordinaryPureMultiplicative_inclusion_isIso
    {B : Grp (Over (Spec (.of R)))} {d : ℕ} (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting R B q n d 0) :
    IsIso (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion R e).hom.hom := by
  let G := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock R q n d
  let H := OrdinaryBlocks.Construction.etaleOrdinaryBlock R q n 0
  let a := (AnnihilatorSheaf.Construction.splitFirstInclusion G H).hom.hom
  let b : (G ⊗ H).X ⟶ G.X := fst G.X H.X
  have hab : a ≫ b = 𝟙 G.X := lift_fst _ _
  have hba : b ≫ a = 𝟙 (G ⊗ H).X := by
    apply CartesianMonoidalCategory.hom_ext
    · change (b ≫ lift (𝟙 G.X) (1 : G.X ⟶ H.X)) ≫ fst G.X H.X = _
      rw [Category.assoc, lift_fst, Category.comp_id, Category.id_comp]
    · exact (etaleZero_points R q n (G ⊗ H).X).elim _ _
  have : IsIso a := ⟨b, hab, hba⟩
  have : IsIso e.inv.hom.hom := inferInstanceAs (IsIso ((Grp.forget _).map e.inv))
  change IsIso (a ≫ e.inv.hom.hom)
  infer_instance

/-- In a pure etale compact block, the chosen subgroup has only the
identity section on every test scheme. -/
theorem ordinaryPureEtale_inclusion_zero
    {B : Grp (Over (Spec (.of R)))} {r : ℕ} (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting R B q n 0 r)
    (T : Over (Spec (.of R))) (a : T ⟶ (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock R q n 0).X) :
    a ≫ (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion R e).hom.hom = 1 := by
  have h : a = 1 := (multiplicativeZero_points R q n T).elim _ _
  exact (congrArg (fun a => a ≫ (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion R e).hom.hom) h).trans
    (MonObj.one_comp _)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactKernels.Construction
