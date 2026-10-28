import OAI.RepresentationTheory.Theta.Geometric.Picard.OpenCoverEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Fppf Picard Locality -/

namespace OAI.RepresentationTheory.Theta.Geometric.FppfPicardLocality

noncomputable section

/-! Actual fppf covers detect equality of Picard sections and locally
lift every test-scheme point through a faithfully flat presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

theorem fppfSingletonOverSieve_mem {S : Scheme.{u}} {U T : Over S} (f : U ⟶ T)
    [Flat f.left] [LocallyOfFinitePresentation f.left] [Surjective f.left] :
    Sieve.ofArrows (fun _ : PUnit.{1} => U) (fun _ => f) ∈ (Scheme.fppfTopology.over S) T := by
  let C : T.left.Cover Scheme.fppfPrecoverage :=
    Scheme.Cover.mkOfCovers PUnit.{1} (fun _ => U.left) (fun _ => f.left)
      (fun x => let ⟨y, hy⟩ := f.left.surjective x; ⟨PUnit.unit, y, hy⟩)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact C.mem_grothendieckTopology

theorem fppfSheaf_map_injective {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) {U T : Over S} (f : U ⟶ T)
    [Flat f.left] [LocallyOfFinitePresentation f.left] [Surjective f.left] :
    Function.Injective (F.obj.map f.op) := by
  intro x y h
  have H : (TypeCat.ofHom (fun _ : PUnit.{u + 2} => x)) =
      TypeCat.ofHom (fun _ : PUnit.{u + 2} => y) := by
    apply F.property.hom_ext_ofArrows (fun _ : PUnit.{1} => f) (fppfSingletonOverSieve_mem f)
    intro i
    ext t
    exact h
  exact congrArg (fun e => e PUnit.unit) H

theorem exists_fppf_test_lift {S : Scheme.{u}} {P' P U : Over S} (p : P' ⟶ P) (f : U ⟶ P)
    [Flat p.left] [LocallyOfFinitePresentation p.left] [Surjective p.left] :
    ∃ (V : Over S) (v : V ⟶ U) (w : V ⟶ P'),
      Flat v.left ∧ LocallyOfFinitePresentation v.left ∧ Surjective v.left ∧ v ≫ f = w ≫ p := by
  let V : Over S := Over.mk (pullback.fst f.left p.left ≫ U.hom)
  let v : V ⟶ U := Over.homMk (pullback.fst f.left p.left)
  let w : V ⟶ P' := Over.homMk (pullback.snd f.left p.left) (by
    rw [← p.w, ← Category.assoc, ← pullback.condition, Category.assoc, f.w]
    rfl)
  refine ⟨V, v, w, ?_, ?_, ?_, ?_⟩
  · exact inferInstanceAs (Flat (pullback.fst f.left p.left))
  · exact inferInstanceAs (LocallyOfFinitePresentation (pullback.fst f.left p.left))
  · exact inferInstanceAs (Surjective (pullback.fst f.left p.left))
  · apply Over.OverMorphism.ext
    exact pullback.condition

end

end OAI.RepresentationTheory.Theta.Geometric.FppfPicardLocality
