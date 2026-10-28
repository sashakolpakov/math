import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Resolution

/-! # Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor.IntrinsicCechFunctor

noncomputable section

/-!
# Functorial Čech cochains with the original coefficient sizes

Morphisms act by their actual restrictions on intersections. The
canonical augmentation is natural in the coefficient presheaf.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry Simplicial

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})

def coefficients : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X ⥤
    X.Opensᵒᵖ ⥤ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X where
  obj := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X
  map f :=
    { app U :=
        { app V := f.app (op (V.unop ⊓ U.unop))
          naturality _ _ g := f.naturality
            (homOfLE (inf_le_inf_right U.unop (leOfHom g.unop))).op }
      naturality _ _ g := by
        apply NatTrans.ext
        funext V
        exact f.naturality (homOfLE (inf_le_inf_left V.unop (leOfHom g.unop))).op }
  map_id _ := by
    apply NatTrans.ext
    funext U
    apply NatTrans.ext
    funext V
    rfl
  map_comp _ _ := by
    apply NatTrans.ext
    funext U
    apply NatTrans.ext
    funext V
    rfl

variable {ι : Type u} (U : ι → X.Opens)

def functor : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X ⥤
    CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) ℕ :=
  coefficients R X ⋙ cechComplexFunctor U

instance additive : (functor R X U).Additive where
  map_add {_P _Q} f g := by
    ext n : 1
    let E := (FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)
    change Limits.Pi.map (fun i : E.I => ((coefficients R X).map (f + g)).app (op (E.obj i))) =
      Limits.Pi.map (fun i : E.I => ((coefficients R X).map f).app (op (E.obj i))) +
        Limits.Pi.map (fun i : E.I => ((coefficients R X).map g).app (op (E.obj i)))
    apply Pi.hom_ext
    intro i
    simp only [Pi.map_π, Preadditive.add_comp]
    rfl

theorem augmentation_naturality {P Q : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X} (f : P ⟶ Q) :
    (CochainComplex.single₀ _).map f ≫ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X U Q =
      AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X U P ≫ (functor R X U).map f := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Augmentation.CechAugmentation.augmentation_f_zero]
  let E := (FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌)
  change f ≫ (Pi.lift (fun i : E.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X Q (E.obj i))) =
    (Pi.lift (fun i : E.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P (E.obj i))) ≫
      Limits.Pi.map (fun i : E.I => ((coefficients R X).map f).app (op (E.obj i)))
  apply Pi.hom_ext
  intro i
  have hmap := Pi.map_π (fun j : E.I => ((coefficients R X).map f).app (op (E.obj j))) i
  have hlift := Pi.lift_comp_π (fun j : E.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P (E.obj j)) i
  have hrestrict : f ≫ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X Q (E.obj i) =
      AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P (E.obj i) ≫
        ((coefficients R X).map f).app (op (E.obj i)) := by
    apply NatTrans.ext
    funext V
    exact (f.naturality (homOfLE (inf_le_left : V.unop ⊓ E.obj i ≤ V.unop)).op).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => f ≫ a)
      (Pi.lift_comp_π (fun j : E.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X Q (E.obj j)) i)).trans
        (hrestrict.trans
          ((congrArg (fun a => a ≫ ((coefficients R X).map f).app (op (E.obj i))) hlift).symm.trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun a =>
                Pi.lift (fun j : E.I => AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.restrictToIntersection R X P (E.obj j)) ≫ a)
                  hmap).symm.trans (Category.assoc _ _ _).symm)))))

def augmentation : CochainComplex.single₀ (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) ⟶ functor R X U where
  app P := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X U P
  naturality _ _ f := augmentation_naturality R X U f

def sheafFunctor : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
    CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙ functor R X U ⋙
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafification R X).mapHomologicalComplex (ComplexShape.up ℕ)

instance sheaf_additive : (sheafFunctor R X U).Additive := by
  unfold sheafFunctor
  infer_instance

def singleIso :
    CochainComplex.single₀ (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ≅
      sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⋙
        CochainComplex.single₀ (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) ⋙
          (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafification R X).mapHomologicalComplex (ComplexShape.up ℕ) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (sheafificationNatIso (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)) (CochainComplex.single₀ _) ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _
            (HomologicalComplex.singleMapHomologicalComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafification R X)
              (ComplexShape.up ℕ) 0).symm

def sheafAugmentation :
    CochainComplex.single₀ (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ⟶
      sheafFunctor R X U :=
  (singleIso R X).hom ≫
    Functor.whiskerLeft (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
      (Functor.whiskerRight (augmentation R X U)
        ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafification R X).mapHomologicalComplex (ComplexShape.up ℕ)))

theorem sheafAugmentation_quasiIso (hU : iSup U = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    QuasiIso ((sheafAugmentation R X U).app F) := by
  have : QuasiIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafAugmentation R X U F.obj) :=
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Resolution.CechResolution.augmentation_quasiIso R X U F.obj hU
  change QuasiIso ((singleIso R X).hom.app F ≫ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.sheafAugmentation R X U F.obj)
  exact quasiIso_comp _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor.IntrinsicCechFunctor
