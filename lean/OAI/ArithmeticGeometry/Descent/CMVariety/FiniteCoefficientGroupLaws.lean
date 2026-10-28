import OAI.ArithmeticGeometry.Descent.CMVariety.BaseChangeMapEquality
import OAI.ArithmeticGeometry.Descent.CMVariety.MonoidalGroupEquations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Finite Coefficient Group Laws -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientGroupLaws.Abelian

noncomputable section

section

/-!
Group preservation of an actual morphism descends from the coefficient
algebra to one finite stage by spreading its unit and multiplication
equations together.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem isMonHom_descends_to_finite_coefficients
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (A : Over (Spec (CommRingCat.of R))) [MonObj A]
    [QuasiCompact A.hom] [LocallyOfFiniteType A.hom] (k : A ⟶ A)
    (h : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map k)) :
    ∃ s : (Finset B)ᵒᵖ, IsMonHom ((Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).map k) := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  have he := (MonoidalGroupEquations.Abelian.isMonHom_map_iff_image_equations F k).mp h
  let source : Bool → Over (Spec (CommRingCat.of R)) := fun i => if i then A ⊗ A else 𝟙_ _
  let a : ∀ i, source i ⟶ A := fun i => match i with
    | false => η[A] ≫ k
    | true => μ[A] ≫ k
  let b : ∀ i, source i ⟶ A := fun i => match i with
    | false => η[A]
    | true => (k ⊗ₘ k) ≫ μ[A]
  have hF (i : Bool) : F.map (a i) = F.map (b i) := by
    cases i
    · exact he.1
    · exact he.2
  let (i : Bool) : QuasiCompact (source i).hom := by
    cases i
    · change QuasiCompact (𝟙 (Spec (CommRingCat.of R)))
      infer_instance
    · change QuasiCompact (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
  obtain ⟨s, hs⟩ := FiniteCoefficientEqualities.Abelian.finite_family_morphism_equalities_descend R B
    (fun i => (source i).left) (fun _ : Bool => A.left)
    (fun i => (source i).hom) (fun _ => A.hom)
    (fun i => (a i).left) (fun i => (b i).left) (fun i => (a i).w) (fun i => (b i).w)
    (fun i => (BaseChangeMapEquality.Abelian.over_baseChange_map_eq_iff _ (a i) (b i)).mp (hF i))
  have hstage (i : Bool) :
      (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).map (a i) =
        (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).map (b i) :=
    (BaseChangeMapEquality.Abelian.over_baseChange_map_eq_iff _ (a i) (b i)).mpr (hs i)
  exact ⟨s, (MonoidalGroupEquations.Abelian.isMonHom_map_iff_image_equations _ k).mpr ⟨hstage false, hstage true⟩⟩

end

/-! All group equations of a finite tuple descend to one coefficient stage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem finite_isMonHom_descends_to_finite_coefficients
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    {Index : Type} [Fintype Index]
    (A : Over (Spec (CommRingCat.of R))) [MonObj A]
    [QuasiCompact A.hom] [LocallyOfFiniteType A.hom] (k : Index → (A ⟶ A))
    (h : ∀ i, IsMonHom
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map (k i))) :
    ∃ s : (Finset B)ᵒᵖ, ∀ i,
      IsMonHom ((Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).map (k i)) := by
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  have he (i : Index) := (MonoidalGroupEquations.Abelian.isMonHom_map_iff_image_equations F (k i)).mp (h i)
  let source : Index × Bool → Over (Spec (CommRingCat.of R)) :=
    fun j => if j.2 then A ⊗ A else 𝟙_ _
  let a : ∀ j, source j ⟶ A := fun j => match j with
    | (i, false) => η[A] ≫ k i
    | (i, true) => μ[A] ≫ k i
  let b : ∀ j, source j ⟶ A := fun j => match j with
    | (_, false) => η[A]
    | (i, true) => (k i ⊗ₘ k i) ≫ μ[A]
  have hF (j : Index × Bool) : F.map (a j) = F.map (b j) := by
    rcases j with ⟨i, j⟩
    cases j
    · exact (he i).1
    · exact (he i).2
  let (j : Index × Bool) : QuasiCompact (source j).hom := by
    rcases j with ⟨i, j⟩
    cases j
    · change QuasiCompact (𝟙 (Spec (CommRingCat.of R)))
      infer_instance
    · change QuasiCompact (pullback.fst A.hom A.hom ≫ A.hom)
      infer_instance
  obtain ⟨s, hs⟩ := FiniteCoefficientEqualities.Abelian.finite_family_morphism_equalities_descend R B
    (fun j => (source j).left) (fun _ : Index × Bool => A.left)
    (fun j => (source j).hom) (fun _ => A.hom)
    (fun j => (a j).left) (fun j => (b j).left) (fun j => (a j).w) (fun j => (b j).w)
    (fun j => (BaseChangeMapEquality.Abelian.over_baseChange_map_eq_iff _ (a j) (b j)).mp (hF j))
  have hstage (j : Index × Bool) :
      (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).map (a j) =
        (Over.pullback (FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s.unop)).map (b j) :=
    (BaseChangeMapEquality.Abelian.over_baseChange_map_eq_iff _ (a j) (b j)).mpr (hs j)
  exact ⟨s, fun i => (MonoidalGroupEquations.Abelian.isMonHom_map_iff_image_equations _ (k i)).mpr
    ⟨hstage (i, false), hstage (i, true)⟩⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientGroupLaws.Abelian
