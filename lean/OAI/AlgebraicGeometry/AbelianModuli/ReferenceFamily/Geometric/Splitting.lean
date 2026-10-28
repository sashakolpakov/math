import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupSplittingAt
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Splitting.GeometricSplitting

noncomputable section

/-! Over a separably closed field the constructed etale group splitting
has a section, so it gives an actual global finite-group trivialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K : Type} [Field K] [IsSepClosed K]
  (H : Over (Spec (.of K))) [GrpObj H]

/-- Finite etale group schemes over a separably closed field are
constant, with the label group constructed from their actual operations. -/
theorem exists_constant_groupIso [IsFinite H.hom] [Etale H.hom] :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), Nonempty
      (HilbertConstruction.Constant.GroupMaps.constantGroupFunctor (Spec (.of K)) G ≅ yonedaGrpObj H) := by
  obtain ⟨T, u, hu, ⟨t, ht⟩, G, hG, hf, ⟨e⟩⟩ :=
    GroupSplittingAt.GroupSplitting.exists_group_splitting_at H (default : Spec (.of K))
  let : Etale u := hu
  obtain ⟨l, hl, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed u (𝟙 _) t ht
  let a := Functor.isoWhiskerLeft (Over.map l).op e
  have hcomp : (Over.map l).op ⋙ ((Over.map u).op ⋙ yonedaGrpObj H) = yonedaGrpObj H := by
    calc
      _ = (Over.map (l ≫ u)).op ⋙ yonedaGrpObj H := by rw [Over.mapComp_eq]; rfl
      _ = yonedaGrpObj H := by rw [hl, Over.mapId_eq]; rfl
  exact ⟨G, hG, hf, ⟨a ≪≫ eqToIso hcomp⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Splitting.GeometricSplitting
