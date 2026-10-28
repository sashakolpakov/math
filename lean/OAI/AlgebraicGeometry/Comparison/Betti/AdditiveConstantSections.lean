import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveConstantExt
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.HomDerived

/-! # Additive Constant Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveConstantSections.Cech

noncomputable section

/-! Hom from the actual constant integers is naturally the complex of global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable (X : TopCat.{0})

abbrev additiveSheaves := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

def constantIntegerHomSectionsEquiv (F : additiveSheaves X) :
    (AdditiveConstantExt.Cech.constantIntegers X ⟶ F) ≃+ F.obj.obj (op ⊤) :=
  (Linear.homCongr ℤ (SheafCohomology.ConstantCoefficients.Projective.constantIntegerUliftIso X) (Iso.refl F)).toAddEquiv.trans
    (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}
      isTerminalTop).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj.obj (op ⊤))))

theorem constantIntegerHomSectionsEquiv_naturality {F G : additiveSheaves X}
    (f : AdditiveConstantExt.Cech.constantIntegers X ⟶ F) (g : F ⟶ G) :
    constantIntegerHomSectionsEquiv X G (f ≫ g) =
      g.hom.app (op ⊤) (constantIntegerHomSectionsEquiv X F f) := by
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop
  let e := SheafCohomology.ConstantCoefficients.Projective.constantIntegerUliftIso X
  change (adj.homEquiv _ G (e.inv ≫ (f ≫ g))) (ULift.up 1) =
    g.hom.app (op ⊤) ((adj.homEquiv _ F (e.inv ≫ f)) (ULift.up 1))
  rw [← Category.assoc, adj.homEquiv_naturality_right]
  rfl

def additiveGlobalSectionsComplex (K : CochainComplex (additiveSheaves X) ℤ) :
    CochainComplex AddCommGrpCat.{0} ℤ :=
  (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).mapHomologicalComplex
    (.up ℤ)).obj K

def constantIntegerHomSectionsComplexIso (K : CochainComplex (additiveSheaves X) ℤ) :
    IntegerAcyclicHomComplex.Ext.integerHomComplex (AdditiveConstantExt.Cech.constantIntegers X) K ≅ additiveGlobalSectionsComplex X K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (constantIntegerHomSectionsEquiv X (K.X n)).toAddCommGrpIso)
    (fun i j _ => by
      ext f
      exact constantIntegerHomSectionsEquiv_naturality X f (K.d i j))

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveConstantSections.Cech
