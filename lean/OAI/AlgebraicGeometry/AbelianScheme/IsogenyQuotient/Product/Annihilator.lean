import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Pairing

/-! # Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Annihilator.Construction

noncomputable section

/-!
The relative annihilator of a product subgroup is the product of the
relative annihilators. Isolating one component proves the difficult
inclusion on every test scheme, including after arbitrary base change.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u v

variable {S : Scheme.{u}} {T W P : Over S} [GrpObj T] [GrpObj W] [IsCommMonObj W]
  {I : Type v} [Fintype I] (G : I → Over S) [∀ i, GrpObj (G i)]
  (D : ∀ X : Over S, (X ⟶ T) ≃* (∀ i, X ⟶ G i))
  (hD : ∀ {X Y : Over S} (f : X ⟶ Y) (x : Y ⟶ T) (i : I),
    D X (f ≫ x) i = f ≫ D Y x i)
  (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := G i) (B := G i) (W := W))

def decomposedRelativeSubgroup (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (G i) P) :
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup T P where
  points X t := (Subgroup.pi Set.univ (fun i => (H i).points X t)).comap (D X).toMonoidHom
  naturality := by
    intro X Y f t x hx
    change ∀ i ∈ Set.univ, D X (f ≫ x) i ∈ (H i).points X (f ≫ t)
    intro i _
    rw [hD]
    exact (H i).naturality f t (hx i (Set.mem_univ i))

omit [Fintype I] in
theorem mem_decomposedRelativeSubgroup
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (G i) P) (X : Over S) (t : X ⟶ P) (x : X ⟶ T) :
    x ∈ (decomposedRelativeSubgroup G D hD H).points X t ↔
      ∀ i, D X x i ∈ (H i).points X t := by
  change (∀ i ∈ Set.univ, D X x i ∈ (H i).points X t) ↔ _
  simp only [Set.mem_univ, forall_const]

omit [Fintype I] in
theorem decomposed_probe_mem [DecidableEq I]
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (G i) P) (X : Over S) (t : X ⟶ P)
    (i : I) (x : X ⟶ G i) (hx : x ∈ (H i).points X t) :
    (D X).symm (Pi.mulSingle i x) ∈ (decomposedRelativeSubgroup G D hD H).points X t := by
  rw [mem_decomposedRelativeSubgroup]
  intro j
  rw [MulEquiv.apply_symm_apply]
  by_cases hji : j = i
  · subst j
    simpa only [Pi.mulSingle_eq_same] using hx
  · simpa only [Pi.mulSingle_eq_of_ne hji] using ((H j).points X t).one_mem

theorem product_pair_probe [DecidableEq I] (X : Over S)
    (i : I) (x : X ⟶ G i) (z : X ⟶ T) :
    (Pairing.Construction.productSchemeBicharacter G D hD e).pairValue ((D X).symm (Pi.mulSingle i x)) z =
      (e i).pairValue x (D X z i) := by
  rw [Pairing.Construction.productSchemeBicharacter_pairValue, MulEquiv.apply_symm_apply]
  rw [Finset.prod_eq_single i]
  · rw [Pi.mulSingle_eq_same]
  · intro j _ hji
    rw [Pi.mulSingle_eq_of_ne hji]
    exact (e j).one_left X _
  · simp

theorem product_relativeAnnihilator
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (G i) P) :
    (Pairing.Construction.productSchemeBicharacter G D hD e).relativeAnnihilator
        (decomposedRelativeSubgroup G D hD H) =
      decomposedRelativeSubgroup G D hD (fun i => (e i).relativeAnnihilator (H i)) := by
  classical
  ext X t z
  rw [mem_decomposedRelativeSubgroup]
  constructor
  · intro hz i Y f x hx
    have hw := decomposed_probe_mem G D hD H Y (f ≫ t) i x hx
    have hv := hz Y f ((D Y).symm (Pi.mulSingle i x)) hw
    rw [product_pair_probe, hD] at hv
    exact hv
  · intro hz Y f w hw
    rw [Pairing.Construction.productSchemeBicharacter_pairValue]
    have hw' := (mem_decomposedRelativeSubgroup G D hD H Y (f ≫ t) w).mp hw
    apply Finset.prod_eq_one
    intro i _
    rw [hD]
    exact hz i Y f (D Y w i) (hw' i)

theorem product_relative_self_annihilating
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (G i) P)
    (hself : ∀ i, (e i).relativeAnnihilator (H i) = H i) :
    (Pairing.Construction.productSchemeBicharacter G D hD e).relativeAnnihilator
        (decomposedRelativeSubgroup G D hD H) =
      decomposedRelativeSubgroup G D hD H := by
  rw [product_relativeAnnihilator]
  simp_rw [hself]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Annihilator.Construction
