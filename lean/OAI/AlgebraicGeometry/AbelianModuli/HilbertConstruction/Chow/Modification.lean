import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeAffineCompactification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProperProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.Closure
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Embedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.Embedding

/-! # Modification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.Modification.ChowModification

noncomputable section

/-! Chow's construction for a proper integral scheme over an arbitrary
affine base, embedded in a finite product of explicit projective closures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

structure Model (f : X ⟶ Spec (.of R)) where
  cover : IntegralFinite.IntegralFiniteAffineCover.Data X
  compactification : ∀ i, Affine.Compactification.AffineCompactification.Data ((cover.opens i).ι ≫ f)
  scheme : Scheme.{u}
  integral : IsIntegral scheme
  projection : scheme ⟶ X
  proper : IsProper projection
  surjective : Surjective projection
  isIso_restrict : IsIso (projection ∣_ cover.common)
  embedding : scheme ⟶
    (∏ᶜ (fun i => Over.mk (compactification i).base)).left
  closedImmersion : IsClosedImmersion embedding
  embedding_base : embedding ≫
      (∏ᶜ (fun i => Over.mk (compactification i).base)).hom =
    projection ≫ f

def build [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsProper f] : Model f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let C := IntegralFinite.IntegralFiniteAffineCover.ofIntegral X
  let D (i : Fin C.n) : Affine.Compactification.AffineCompactification.Data ((C.opens i).ι ≫ f) := by
    have : IsAffine (C.opens i).toScheme := C.affine i
    exact Finite.TypeAffineCompactification.AffineCompactification.ofAffineFiniteType ((C.opens i).ι ≫ f)
  let P : Fin C.n → Over (Spec (.of R)) := fun i => Over.mk (D i).base
  let B := ∏ᶜ P
  have : IsProper B.hom := Finite.ProperProducts.overFinProduct_proper C.n P (fun i => (D i).proper)
  have : Nonempty C.common := C.common_nonempty
  have : IsAffine C.common.toScheme := C.common_affine
  let T := Over.mk (C.common.ι ≫ f)
  let a (i : Fin C.n) : T ⟶ P i :=
    Over.homMk (X.homOfLE (C.common_le i) ≫ (D i).chart) (by
      change (X.homOfLE (C.common_le i) ≫ (D i).chart) ≫ (D i).base = C.common.ι ≫ f
      rw [Category.assoc, (D i).chart_base, ← Category.assoc, X.homOfLE_ι])
  let j := (Pi.lift a).left
  have hj : C.common.ι ≫ f = j ≫ B.hom := (Over.w (Pi.lift a)).symm
  let Z := Graph.Closure.GraphClosure.scheme f B.hom C.common j hj
  let q := Graph.Closure.GraphClosure.projection f B.hom C.common j hj
  let g := Graph.Closure.GraphClosure.map f B.hom C.common j hj
  let t := Graph.Closure.GraphClosure.chart f B.hom C.common j hj
  have hZ : IsIntegral Z := Graph.Closure.GraphClosure.integral f B.hom C.common j hj
  have hq : IsProper q := Graph.Closure.GraphClosure.proper f B.hom C.common j hj
  have hg : IsProper g := Graph.Closure.GraphClosure.map_isProper f B.hom C.common j hj
  have ht : IsDominant t := Graph.Closure.GraphClosure.dominant f B.hom C.common j hj
  have hpair : IsClosedImmersion (prod.lift q g) :=
    Pullback.Embedding.PullbackEmbedding.pair_of_closed f B.hom (Graph.Closure.GraphClosure.graph f B.hom C.common j hj).imageι
  have hsep (i : Fin C.n) : (D i).scheme.IsSeparated := by
    have : IsProper (D i).base := (D i).proper
    exact ⟨by rw [← terminal.comp_from (D i).base]; infer_instance⟩
  have hopen (i : Fin C.n) : IsOpenImmersion (D i).chart := (D i).openImmersion
  have hclosed : IsClosedImmersion g := by
    apply Embedding.ChowEmbedding.closed q g C.opens C.covers (fun i => (D i).scheme)
      (fun i => (D i).chart) (fun i => (Pi.π P i).left)
      t (fun i => X.homOfLE (C.common_le i))
    · intro i
      exact (Graph.Closure.GraphClosure.chart_projection f B.hom C.common j hj).trans (X.homOfLE_ι _).symm
    · intro i
      change Graph.Closure.GraphClosure.chart f B.hom C.common j hj ≫
        Graph.Closure.GraphClosure.map f B.hom C.common j hj ≫ (Pi.π P i).left = _
      rw [← Category.assoc, Graph.Closure.GraphClosure.chart_map]
      exact congrArg Over.Hom.left (Pi.lift_comp_π a i)
  exact ⟨C, D, Z, hZ, q, hq, Graph.Closure.GraphClosure.surjective f B.hom C.common j hj,
    Graph.Closure.GraphClosure.isIso_restrict f B.hom C.common j hj, g, hclosed,
    Graph.Closure.GraphClosure.map_base f B.hom C.common j hj⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.Modification.ChowModification
