import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BranchSplitting

/-! # Constant Permutations -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConstantPermutations

noncomputable section

/-! An isomorphism between constant finite schemes is a locally constant
permutation of their sheets, on arbitrary (possibly nonreduced) bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {I J : Type u}

theorem constantScheme_point_reconstruction (y : (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).left) :
    Sigma.ι (fun _ : I => S) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex S I y) ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom y) = y := by
  obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk (fun _ : I => S)).surjective y
  rw [sigmaMk_mk, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι]
  have h := congrArg (fun f : S ⟶ S => f x) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom (S := S) i)
  change (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom (Sigma.ι (fun _ : I => S) i x) = x at h
  rw [h]

def constantIsoIndex (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I ≅ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S J) (i : I) :
    LocallyConstant S J :=
  AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (Over.mk (𝟙 S)) (BranchSplitting.constantCoproductInclusion S I i ≫ e.hom)

theorem constantIsoIndex_point (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I ≅ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S J)
    (i : I) (x : S) :
    e.hom.left (Sigma.ι (fun _ : I => S) i x) =
      Sigma.ι (fun _ : J => S) (constantIsoIndex e i x) x := by
  have h := constantScheme_point_reconstruction (e.hom.left (Sigma.ι (fun _ : I => S) i x))
  have hb := congrArg (fun f : S ⟶ S => f x)
    (BranchSplitting.constantCoproductInclusion S I i ≫ e.hom).w
  change (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S J).hom (e.hom.left (Sigma.ι (fun _ : I => S) i x)) = x at hb
  rw [hb] at h
  exact h.symm

theorem constantIsoIndex_inverse (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I ≅ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S J)
    (i : I) (x : S) : constantIsoIndex e.symm (constantIsoIndex e i x) x = i := by
  have h := congrArg (fun f : (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).left ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).left =>
    f (Sigma.ι (fun _ : I => S) i x)) (congrArg (fun f => f.left) e.hom_inv_id)
  change e.inv.left (e.hom.left (Sigma.ι (fun _ : I => S) i x)) =
    Sigma.ι (fun _ : I => S) i x at h
  rw [constantIsoIndex_point e, ← Iso.symm_hom, constantIsoIndex_point e.symm] at h
  simpa only [AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι] using congrArg (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex S I) h

def constantIsoPermutation [Finite I] (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I ≅ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S J) :
    LocallyConstant S (I ≃ J) :=
  LocallyConstant.desc (fun x => {
    toFun := fun i => constantIsoIndex e i x
    invFun := fun j => constantIsoIndex e.symm j x
    left_inv := fun i => constantIsoIndex_inverse e i x
    right_inv := fun j => constantIsoIndex_inverse e.symm j x })
    (LocallyConstant.unflip (constantIsoIndex e)) rfl
    (fun _ _ h => Equiv.ext (congrFun h))

@[simp] theorem constantIsoPermutation_apply [Finite I]
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I ≅ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S J) (x : S) (i : I) :
    constantIsoPermutation e x i = constantIsoIndex e i x := rfl

/-- On the open set with a fixed sheet permutation, the isomorphism is
literally that permutation as a scheme morphism. No reduction is taken. -/
theorem constantIsoPermutation_restrict [Finite I]
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I ≅ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S J) (p : I ≃ J) (i : I) :
    (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (constantIsoPermutation e) p).ι ≫
        Sigma.ι (fun _ : I => S) i ≫ e.hom.left =
      (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (constantIsoPermutation e) p).ι ≫ Sigma.ι (fun _ : J => S) (p i) := by
  let U := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (constantIsoPermutation e) p
  have hf := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_factor (U.ι ≫ Sigma.ι (fun _ : I => S) i ≫ e.hom.left) (p i)
    (fun x => congrArg (fun a : I ≃ J => a i) x.property)
  have hb : (Sigma.ι (fun _ : I => S) i ≫ e.hom.left) ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S J).hom = 𝟙 S :=
    (BranchSplitting.constantCoproductInclusion S I i ≫ e.hom).w
  simpa only [Category.assoc, hb, Category.comp_id] using hf

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ConstantPermutations
