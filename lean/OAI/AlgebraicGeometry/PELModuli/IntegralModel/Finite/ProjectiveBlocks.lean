import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointProjectiveBlocks
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DisjointClosedCoproduct
import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts
import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective

/-! # Projective Blocks -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ProjectiveBlocks

noncomputable section

/-! Construct one actual projective embedding for a finite coproduct
of projective varieties by assigning disjoint coordinate blocks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective

theorem finite_projective_varieties_embedding {I : Type} [Finite I]
    (V : I → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ∃ (n : ℕ) (e : (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigma (fun i => (V i).toOver)).left ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n),
      IsClosedImmersion e ∧
      e ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = (ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigma (fun i => (V i).toOver)).hom := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let J := Σ i : I, Fin ((V i).ambientDimension + 1)
  let n := Fintype.card J
  let j (i : I) (a : Fin ((V i).ambientDimension + 1)) : Fin (n + 1) :=
    ((Fintype.equivFin J) ⟨i, a⟩).castSucc
  have hj (i : I) : Function.Injective (j i) := by
    intro a b h
    exact eq_of_heq ((Sigma.mk.inj_iff.mp ((Fintype.equivFin J).injective
      (Fin.castSucc_injective _ h))).2)
  have hd : Pairwise (fun i k => Disjoint (Set.range (j i)) (Set.range (j k))) := by
    intro i k hik
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, h⟩
    have he := (Fintype.equivFin J).injective (Fin.castSucc_injective _ h)
    exact hik (congrArg Sigma.fst he).symm
  let f (i : I) : (V i).carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n :=
    (V i).embedding ≫ IntersectionTheory.ProjectionFormula.CoordinateBlockMap.map (j i) (hj i)
  have hf (i : I) : IsClosedImmersion (f i) :=
    inferInstanceAs (IsClosedImmersion ((V i).embedding ≫ IntersectionTheory.ProjectionFormula.CoordinateBlockMap.map (j i) (hj i)))
  have hdis : Pairwise (fun i k => Disjoint (Set.range (f i)) (Set.range (f k))) := by
    intro i k hik
    exact (IntersectionTheory.ProjectionFormula.DisjointProjectiveBlocks.disjoint (j i) (hj i) (j k) (hj k) (hd hik)).mono
      (by rintro _ ⟨x, rfl⟩; exact ⟨(V i).embedding x, rfl⟩)
      (by rintro _ ⟨x, rfl⟩; exact ⟨(V k).embedding x, rfl⟩)
  refine ⟨n, Sigma.desc f, @DisjointClosedCoproduct.finite_disjoint_closed_sigmaDesc I inferInstance
    (fun i => (V i).carrier) (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) f hf hdis, ?_⟩
  change Sigma.desc f ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = Sigma.desc (fun i => (V i).structureMap)
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_comp_desc_assoc]
  change ((V i).embedding ≫ IntersectionTheory.ProjectionFormula.CoordinateBlockMap.map (j i) (hj i)) ≫
    Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = Sigma.ι (fun i => (V i).carrier) i ≫
      Sigma.desc (fun i => (V i).structureMap)
  rw [Category.assoc, IntersectionTheory.ProjectionFormula.CoordinateBlockMap.over_base, (V i).embedding_over, Sigma.ι_comp_desc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ProjectiveBlocks
