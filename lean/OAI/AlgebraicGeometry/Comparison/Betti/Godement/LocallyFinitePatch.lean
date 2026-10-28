import OAI.AlgebraicGeometry.Comparison.Betti.Godement.SupportedLiftControl
import OAI.AlgebraicGeometry.Comparison.Betti.FamilyLocallyFiniteSum
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.LocalSumIdentity

/-! # Locally Finite Patch -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.LocallyFinitePatch

noncomputable section

/-! Locally finite supported endomorphisms patch local lifts in every
degree of the original Godement resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped BigOperators

variable {X : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℂ) X}

theorem godement_locally_finite_partition_lift {ι : Type*}
    (U V : ι → Opens X) (hcover : ∀ i, U i ⊔ V i = ⊤)
    (f : ι → (F ⟶ F)) (hf : ∀ i, Locality.VanishesOn (f i) (V i))
    (hlocal : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∃ s : Finset ι,
      (∀ i, i ∉ s → W ≤ V i) ∧ Locality.VanishesOn ((∑ i ∈ s, f i) - 𝟙 _) W)
    (n : ℕ) (z : ((Resolution.godementComplex X F).X (n + 1)).obj.obj (op ⊤))
    (a : ∀ i, ((Resolution.godementComplex X F).X n).obj.obj (op (U i)))
    (ha : ∀ i, ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op (U i)) (a i) =
      ((Resolution.godementComplex X F).X (n + 1)).obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op z) :
    ∃ t : ((Resolution.godementComplex X F).X n).obj.obj (op ⊤),
      ((Resolution.godementComplex X F).d n (n + 1)).hom.app (op ⊤) t = z := by
  classical
  choose t ht htV using fun i => SupportedLiftControl.godement_supported_local_lift_control (f i) (U i) (V i)
    (hcover i) (hf i) n z (a i) (ha i)
  refine ⟨FamilyLocallyFiniteSum.Godement.stalkFamilySum t, ?_⟩
  funext x
  obtain ⟨W, hxW, s, hs, hsum⟩ := hlocal x.val
  let K := Resolution.godementComplex X F
  let r₀ := (K.X n).obj.map (homOfLE (show W ≤ ⊤ from le_top)).op
  let r₁ := (K.X (n + 1)).obj.map (homOfLE (show W ≤ ⊤ from le_top)).op
  let d := K.d n (n + 1)
  have hn (b : (K.X n).obj.obj (op ⊤)) :
      d.hom.app (op W) (r₀ b) = r₁ (d.hom.app (op ⊤) b) :=
    ConcreteCategory.congr_hom (d.hom.naturality (homOfLE (show W ≤ ⊤ from le_top)).op) b
  have hr : r₀ (FamilyLocallyFiniteSum.Godement.stalkFamilySum t) = ∑ i ∈ s, r₀ (t i) :=
    FamilyLocallyFiniteSum.Godement.stalkFamilySum_restrict t W s (fun i hi y hy => htV i y (hs i hi hy))
  have hterm (i : ι) :
      r₁ (d.hom.app (op ⊤) (t i)) =
        ((Resolution.godementTerm X (n + 1)).map (f i)).hom.app (op W) (r₁ z) := by
    rw [show d.hom.app (op ⊤) (t i) =
      ((Resolution.godementTerm X (n + 1)).map (f i)).hom.app (op ⊤) z from ht i]
    exact (ConcreteCategory.congr_hom
      (((Resolution.godementTerm X (n + 1)).map (f i)).hom.naturality
        (homOfLE (show W ≤ ⊤ from le_top)).op) z).symm
  have he : r₁ (d.hom.app (op ⊤) (FamilyLocallyFiniteSum.Godement.stalkFamilySum t)) = r₁ z := calc
    _ = d.hom.app (op W) (r₀ (FamilyLocallyFiniteSum.Godement.stalkFamilySum t)) := (hn _).symm
    _ = ∑ i ∈ s, d.hom.app (op W) (r₀ (t i)) := by rw [hr, map_sum]
    _ = ∑ i ∈ s, r₁ (d.hom.app (op ⊤) (t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hn (t i)
    _ = ∑ i ∈ s, (show (K.X (n + 1)).obj.obj (op W) from
        ((Resolution.godementTerm X (n + 1)).map (f i)).hom.app (op W) (r₁ z)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = r₁ z := LocalSumIdentity.godementTerm_local_sum f s W hsum (n + 1) (r₁ z)
  exact congrFun he ⟨x.val, hxW⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.LocallyFinitePatch
