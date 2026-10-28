import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Image
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CoefficientComposition
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.OpenCoefficientNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso

/-! # Global Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.GlobalImage.CechGlobalImage

noncomputable section

/-! Taking global sections of the actual Čech direct-image comparison gives the original comparison on inverse-image opens. -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

theorem five_factors {K : Type*} [Category* K] {A B C D E F G H I : K}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E) (e : E ⟶ F)
    (u : A ⟶ G) (α : B ⟶ H) (β : C ⟶ H) (p : G ⟶ H) (q : H ⟶ E)
    (v : G ⟶ I) (t : H ⟶ I) (w : I ⟶ F)
    (h₁ : a ≫ α = u ≫ p) (h₂ : b ≫ β = α) (h₃ : c ≫ d = β ≫ q)
    (h₄ : q ≫ e = t ≫ w) (h₅ : p ≫ t = v) :
    (a ≫ b ≫ c) ≫ (d ≫ e) = (u ≫ v) ≫ w := by
  calc
    (a ≫ b ≫ c) ≫ (d ≫ e) = (a ≫ b) ≫ (c ≫ d) ≫ e := by simp only [Category.assoc]
    _ = (a ≫ b) ≫ (β ≫ q) ≫ e := by rw [h₃]
    _ = (a ≫ (b ≫ β)) ≫ (q ≫ e) := by simp only [Category.assoc]
    _ = (a ≫ α) ≫ (t ≫ w) := by rw [h₂, h₄]
    _ = (u ≫ p) ≫ (t ≫ w) := by rw [h₁]
    _ = (u ≫ (p ≫ t)) ≫ w := by simp only [Category.assoc]
    _ = (u ≫ v) ≫ w := by rw [h₅]

variable (R : Type) [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X.left)

theorem coefficient_triangle :
    Functor.whiskerRight (Image.CechImage.coefficientsIso R f.left P).hom
        ((evaluation Y.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)) ≫
      Functor.whiskerLeft (Image.CechImage.preimage f.left).op (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.coefficientIso R X P).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.coefficientIso R Y ((Image.CechImage.functor R f.left).obj P)).hom := by
  apply NatTrans.ext
  funext U
  change 𝟙 _ ≫ P.map _ = P.map _
  exact (Category.id_comp _).trans (congrArg P.map (Subsingleton.elim _ _))

theorem square {ι : Type} (U : ι → Y.left.Opens) :
    (((evaluation Y.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).map
        (Image.CechImage.complexIso R f.left U P).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X (fun i => f.left ⁻¹ᵁ U i) P).hom =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R Y U ((Image.CechImage.functor R f.left).obj P)).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Image.CechImage.preimage f.left) U P).hom := by
  let F := Image.CechImage.preimage f.left
  let D := Image.CechImage.functor R f.left
  let EX := (evaluation X.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)
  let EY := (evaluation Y.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)
  let EYc := EY.mapHomologicalComplex (.up ℕ)
  let EXc := EX.mapHomologicalComplex (.up ℕ)
  let Dc := D.mapHomologicalComplex (.up ℕ)
  let Q := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X.left P
  let B := F.op ⋙ Q
  let A := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R Y.left (D.obj P)
  let E := (FormalCoproduct.mk ι U).cech
  let EF := (FormalCoproduct.mk ι (fun i => f.left ⁻¹ᵁ U i)).cech
  let CY := cechComplexFunctor (A := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y.left) U
  let I := cechComplexFunctor (A := ModuleCat.{0} R) U
  let J := cechComplexFunctor (A := ModuleCat.{0} R) (fun i => f.left ⁻¹ᵁ U i)
  let a := Image.CechImage.coefficientsIso R f.left P
  let c := AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.coefficientIso R X P
  let cY := AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.coefficientIso R Y (D.obj P)
  let d := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso D E B
  let eY := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso EY E A
  let eBD := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso EY E (B ⋙ D)
  let eBX := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso EX E B
  let eQX := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso EX EF Q
  let bcQ := AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U Q
  let bcP := AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U P
  let bcQX := AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U (Q ⋙ EX)
  let φ := I.map (Functor.whiskerRight a.hom EY)
  let ψ := I.map (Functor.whiskerLeft F.op c.hom)
  have h₁ := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.naturality EY E a.hom
  have h₂ : EYc.map d.inv ≫ eBX.hom = eBD.hom :=
    (EYc.mapIso d).inv_comp_eq.mpr (CoefficientComposition.CechCoefficientComposition.hom D EY E B).symm
  have h₃ := OpenCoefficientNaturality.CechOpenCoefficientNaturality.naturality F EX U Q
  have h₄ := (OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.naturality F U c.hom).symm
  have h₅ : φ ≫ ψ = I.map cY.hom :=
    (I.map_comp _ _).symm.trans (congrArg I.map (coefficient_triangle R f P))
  have hm : EYc.map ((CY.map a.hom) ≫ d.inv ≫ Dc.map bcQ.hom) =
      EYc.map (CY.map a.hom) ≫ EYc.map d.inv ≫ EXc.map bcQ.hom :=
    (EYc.map_comp _ _).trans (congrArg (fun k => EYc.map (CY.map a.hom) ≫ k) (EYc.map_comp _ _))
  exact (congrArg (fun k => k ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X (fun i => f.left ⁻¹ᵁ U i) P).hom) hm).trans
    (five_factors (EYc.map (CY.map a.hom)) (EYc.map d.inv) (EXc.map bcQ.hom) eQX.hom (J.map c.hom)
      eY.hom eBD.hom eBX.hom φ bcQX.hom (I.map cY.hom) ψ bcP.hom h₁ h₂ h₃ h₄ h₅)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.GlobalImage.CechGlobalImage
