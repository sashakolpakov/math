import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReducedHeightOneMaps
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Multiplicative

/-! # Ordinary Etale Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryEtaleTransport.Construction

noncomputable section

/-!
The etale factor in a split ordinary q-torsion group is intrinsic.
Every native group map preserves its inclusion; the possible cross map
into the multiplicative factor vanishes on the reduced etale source.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable (q : ℕ) [Fact q.Prime] (k : Type u) [Field k] [CharP k q]
variable {G G' : Grp (Over (Spec (.of k)))} {d r d' r' : ℕ}
variable (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q 1 d r)
variable (e' : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G' q 1 d' r')

/-- The original etale factor embedded in its source block. -/
def ordinaryEtaleInclusion : OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r ⟶ G :=
  AnnihilatorSheaf.Construction.splitSecondInclusion (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 d) (OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r) ≫ e.inv

/-- The etale-factor projection in the chosen coordinates. -/
def ordinaryEtaleProjection : G ⟶ OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r :=
  e.hom ≫ Grp.homMk (snd (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 d).X (OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r).X)

omit [Fact q.Prime] [CharP k q] in
theorem ordinaryEtaleInclusion_projection :
    ordinaryEtaleInclusion q k e ≫ ordinaryEtaleProjection q k e = 𝟙 _ := by
  apply Grp.hom_ext
  change ((AnnihilatorSheaf.Construction.splitSecondInclusion _ _).hom.hom ≫ e.inv.hom.hom) ≫
    (e.hom.hom.hom ≫ snd _ _) = 𝟙 _
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ := ((Grp.forget _).mapIso e).inv_hom_id
  rw [Category.assoc, ← Category.assoc e.inv.hom.hom, he, Category.id_comp]
  exact lift_snd _ _

instance ordinaryEtaleInclusion_mono : Mono (ordinaryEtaleInclusion q k e) :=
  mono_of_mono_fac (ordinaryEtaleInclusion_projection q k e)

instance ordinaryEtaleInclusion_mono_underlying : Mono (ordinaryEtaleInclusion q k e).hom.hom :=
  mono_of_mono_fac (congrArg (fun f : OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r ⟶ OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r => f.hom.hom)
    (ordinaryEtaleInclusion_projection q k e))

variable (a : G ⟶ G')

/-- The induced map on the actual etale factors. -/
def ordinaryEtaleMap : OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r ⟶ OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r' :=
  ordinaryEtaleInclusion q k e ≫ a ≫ ordinaryEtaleProjection q k e'

/-- The etale factor is preserved by every native group homomorphism,
independently of which ordinary splittings were used. -/
theorem ordinaryEtaleMap_inclusion :
    ordinaryEtaleMap q k e e' a ≫ ordinaryEtaleInclusion q k e' =
      ordinaryEtaleInclusion q k e ≫ a := by
  let M := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 d'
  let E := OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r'
  let E₀ := OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r
  let t : E₀.X ⟶ M.X ⊗ E.X :=
    (ordinaryEtaleInclusion q k e).hom.hom ≫ a.hom.hom ≫ e'.hom.hom.hom
  have : Etale E₀.X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  have : IsReduced E₀.X.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field E₀.X.hom
  have ht : t ≫ fst M.X E.X = 1 :=
    ReducedHeightOneMaps.Construction.map_from_reduced_of_trivial_frobenius q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) _
      (Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius q k d')
  have hfac : (t ≫ snd M.X E.X) ≫ (AnnihilatorSheaf.Construction.splitSecondInclusion M E).hom.hom = t := by
    apply CartesianMonoidalCategory.hom_ext
    · change ((t ≫ snd M.X E.X) ≫ lift (1 : E.X ⟶ M.X) (𝟙 E.X)) ≫ fst M.X E.X = _
      rw [Category.assoc, lift_fst, MonObj.comp_one]
      exact ht.symm
    · change ((t ≫ snd M.X E.X) ≫ lift (1 : E.X ⟶ M.X) (𝟙 E.X)) ≫ snd M.X E.X = _
      rw [Category.assoc, lift_snd, Category.comp_id]
  apply Grp.hom_ext
  have htmap : (ordinaryEtaleMap q k e e' a).hom.hom = t ≫ snd M.X E.X := by
    change (ordinaryEtaleInclusion q k e).hom.hom ≫ a.hom.hom ≫
      (e'.hom.hom.hom ≫ snd M.X E.X) = _
    simp only [t, Category.assoc]
  have he' : e'.hom.hom.hom ≫ e'.inv.hom.hom = 𝟙 G'.X :=
    ((Grp.forget _).mapIso e').hom_inv_id
  change (ordinaryEtaleMap q k e e' a).hom.hom ≫
    ((AnnihilatorSheaf.Construction.splitSecondInclusion M E).hom.hom ≫ e'.inv.hom.hom) = _
  rw [htmap, ← Category.assoc, hfac]
  change ((ordinaryEtaleInclusion q k e).hom.hom ≫ a.hom.hom ≫ e'.hom.hom.hom) ≫
    e'.inv.hom.hom = (ordinaryEtaleInclusion q k e).hom.hom ≫ a.hom.hom
  rw [Category.assoc, Category.assoc, he', Category.comp_id]

omit [Fact q.Prime] [CharP k q] in
theorem ordinaryEtaleMap_id : ordinaryEtaleMap q k e e (𝟙 G) = 𝟙 _ := by
  change ordinaryEtaleInclusion q k e ≫ 𝟙 G ≫ ordinaryEtaleProjection q k e = _
  rw [Category.id_comp, ordinaryEtaleInclusion_projection]

variable {G'' : Grp (Over (Spec (.of k)))} {d'' r'' : ℕ}
variable (e'' : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G'' q 1 d'' r'') (b : G' ⟶ G'')

theorem ordinaryEtaleMap_comp :
    ordinaryEtaleMap q k e e' a ≫ ordinaryEtaleMap q k e' e'' b =
      ordinaryEtaleMap q k e e'' (a ≫ b) := by
  apply (cancel_mono (ordinaryEtaleInclusion q k e'')).mp
  let x := ordinaryEtaleMap q k e e' a
  let y := ordinaryEtaleMap q k e' e'' b
  let j := ordinaryEtaleInclusion q k e
  let j' := ordinaryEtaleInclusion q k e'
  let j'' := ordinaryEtaleInclusion q k e''
  exact (Category.assoc x y j'').trans
    ((congrArg (fun z => x ≫ z) (ordinaryEtaleMap_inclusion q k e' e'' b)).trans
      ((Category.assoc x j' b).symm.trans
        ((congrArg (fun z => z ≫ b) (ordinaryEtaleMap_inclusion q k e e' a)).trans
          ((Category.assoc j a b).trans (ordinaryEtaleMap_inclusion q k e e'' (a ≫ b)).symm))))

/-- Native source isomorphisms induce actual etale-factor isomorphisms. -/
def ordinaryEtaleIso (a : G ≅ G') :
    OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r ≅ OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r' where
  hom := ordinaryEtaleMap q k e e' a.hom
  inv := ordinaryEtaleMap q k e' e a.inv
  hom_inv_id := (ordinaryEtaleMap_comp q k e e' a.hom e a.inv).trans
    ((congrArg (ordinaryEtaleMap q k e e) a.hom_inv_id).trans (ordinaryEtaleMap_id q k e))
  inv_hom_id := (ordinaryEtaleMap_comp q k e' e a.inv e' a.hom).trans
    ((congrArg (ordinaryEtaleMap q k e' e') a.inv_hom_id).trans (ordinaryEtaleMap_id q k e'))

theorem ordinaryEtaleIso_inclusion (a : G ≅ G') :
    (ordinaryEtaleIso q k e e' a).hom ≫ ordinaryEtaleInclusion q k e' =
      ordinaryEtaleInclusion q k e ≫ a.hom :=
  ordinaryEtaleMap_inclusion q k e e' a.hom

/-- The entire embedded etale q-torsion subgroup is independent of
its ordinary coordinate splitting. -/
theorem ordinaryEtaleSubobject_independent
    (e₂ : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q 1 d' r') :
    Subobject.mk (ordinaryEtaleInclusion q k e).hom.hom =
      Subobject.mk (ordinaryEtaleInclusion q k e₂).hom.hom := by
  have : Mono (ordinaryEtaleInclusion q k e).hom.hom :=
    ordinaryEtaleInclusion_mono_underlying q k e
  have : Mono (ordinaryEtaleInclusion q k e₂).hom.hom :=
    ordinaryEtaleInclusion_mono_underlying q k e₂
  let a := (Grp.forget (Over (Spec (.of k)))).mapIso (ordinaryEtaleIso q k e e₂ (Iso.refl G))
  refine Subobject.mk_eq_mk_of_comm (ordinaryEtaleInclusion q k e).hom.hom
    (ordinaryEtaleInclusion q k e₂).hom.hom a ?_
  exact (congrArg (fun z : OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r ⟶ G => z.hom.hom)
    (ordinaryEtaleIso_inclusion q k e e₂ (Iso.refl G))).trans
    (Category.comp_id _)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryEtaleTransport.Construction
