import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PicardMaps

/-! # Dual Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison

noncomputable section

/-!
The actual dual morphism constructed by representing pullback of homogeneous
Picard classes. Isomorphisms, composition, and the origin are proved from
this construction. No map of dual schemes or compatibility is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PicardMaps

variable {S : Scheme.{u}} {a b c : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b S} {C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme c S}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (DC : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData C)

def dualMap (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    DB.abelian.scheme ⟶ DA.abelian.scheme :=
  DA.representable.homEquiv.symm
    ((PicardMaps.homogeneousPicardSheafPull f).hom.app (op DB.abelian.scheme)
      (DB.representable.homEquiv (𝟙 DB.abelian.scheme)))

theorem dualMap_action (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} (x : T ⟶ DB.abelian.scheme) :
    DA.representable.homEquiv (x ≫ dualMap DA DB f) =
      (PicardMaps.homogeneousPicardSheafPull f).hom.app (op T) (DB.representable.homEquiv x) := by
  rw [DA.representable.homEquiv_comp]
  dsimp only [dualMap]
  rw [Equiv.apply_symm_apply]
  rw [← (PicardMaps.homogeneousPicardSheafPull f).hom.naturality_apply x.op]
  rw [← DB.representable.homEquiv_comp x (𝟙 DB.abelian.scheme), Category.comp_id]

theorem dualMap_unique (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (d : DB.abelian.scheme ⟶ DA.abelian.scheme)
    (hd : ∀ (T : Over S) (x : T ⟶ DB.abelian.scheme),
      DA.representable.homEquiv (x ≫ d) =
        (PicardMaps.homogeneousPicardSheafPull f).hom.app (op T) (DB.representable.homEquiv x)) :
    d = dualMap DA DB f := by
  apply DA.representable.homEquiv.injective
  simpa only [Category.id_comp] using
    (hd DB.abelian.scheme (𝟙 _)).trans (dualMap_action DA DB f (𝟙 _)).symm

theorem dualMap_id : dualMap DA DA (𝟙 A.scheme) = 𝟙 DA.abelian.scheme := by
  apply DA.representable.homEquiv.injective
  dsimp only [dualMap]
  rw [Equiv.apply_symm_apply, PicardMaps.homogeneousPicardSheafPull_id]
  rfl

theorem dualMap_comp (f : A.scheme ⟶ B.scheme) (g : B.scheme ⟶ C.scheme)
    [IsMonHom f] [IsMonHom g] :
    dualMap DA DC (f ≫ g) = dualMap DB DC g ≫ dualMap DA DB f := by
  symm
  apply dualMap_unique DA DC (f ≫ g)
  intro T x
  rw [← Category.assoc, dualMap_action, dualMap_action]
  exact (congrArg (fun z => z.hom.app (op T) (DC.representable.homEquiv x))
    (PicardMaps.homogeneousPicardSheafPull_comp f g))

def dualIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    DB.abelian.scheme ≅ DA.abelian.scheme where
  hom := dualMap DA DB e.hom
  inv := dualMap DB DA e.inv
  hom_inv_id := by
    rw [← dualMap_comp]
    simp only [e.inv_hom_id, dualMap_id]
  inv_hom_id := by
    rw [← dualMap_comp]
    simp only [e.hom_inv_id, dualMap_id]

theorem dualMap_origin (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (T : Over S) : (1 : T ⟶ DB.abelian.scheme) ≫ dualMap DA DB f = 1 := by
  apply DA.representable.homEquiv.injective
  rw [dualMap_action, DB.origin, DA.origin, PicardMaps.homogeneousPicardSheafPull_trivial]

/-- The universal class evaluated at a morphism is the actual pullback
of the Poincare line bundle, followed by homogeneous sheafification. -/
theorem representable_poincare {T : Over S} (d : T ⟶ DA.abelian.scheme) :
    DA.representable.homEquiv d =
      (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (op T)
        (A.homogeneousPicardPresheaf.map d.op
          ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare, DA.poincareHomogeneous⟩) := by
  have h := DA.representable.homEquiv_comp d (𝟙 DA.abelian.scheme)
  rw [Category.comp_id, DA.universalClass] at h
  exact h.trans (((toSheafify (Scheme.fppfTopology.over S)
    A.homogeneousPicardPresheaf).naturality_apply d.op
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare, DA.poincareHomogeneous⟩).symm)

/-- A dual morphism specified by the native Poincare equation agrees with
the dual morphism constructed from Picard pullback. -/
theorem dualMap_eq_of_poincare (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (d : DB.abelian.scheme ⟶ DA.abelian.scheme)
    (hp : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ f).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare)) :
    d = dualMap DA DB f := by
  let qA : A.homogeneousPicardPresheaf.obj (op DA.abelian.scheme) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare, DA.poincareHomogeneous⟩
  let qB : B.homogeneousPicardPresheaf.obj (op DB.abelian.scheme) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare, DB.poincareHomogeneous⟩
  have hq : A.homogeneousPicardPresheaf.map d.op qA =
      (PicardMaps.homogeneousPicardPull f).app (op DB.abelian.scheme) qB := Subtype.ext hp.symm
  apply DA.representable.homEquiv.injective
  exact (representable_poincare DA d).trans
    ((congrArg ((toSheafify (Scheme.fppfTopology.over S)
      A.homogeneousPicardPresheaf).app (op DB.abelian.scheme)) hq).trans
    ((ConcreteCategory.congr_hom
      (NatTrans.congr_app (PicardMaps.homogeneousPicardPull_toSheaf f) (op DB.abelian.scheme)) qB).trans
    ((congrArg ((PicardMaps.homogeneousPicardSheafPull f).hom.app (op DB.abelian.scheme))
      DB.universalClass.symm).trans
      (DA.representable.homEquiv.apply_symm_apply _).symm)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison
