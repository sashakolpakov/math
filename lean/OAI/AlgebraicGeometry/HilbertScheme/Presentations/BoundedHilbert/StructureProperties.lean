import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Immersion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.BaseChange

/-! # Structure Properties -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.StructureProperties.GradedHilbert

noncomputable section

/-! The constructed bounded Hilbert scheme is separated and of finite
type over its base, before applying the valuative existence criterion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.BaseChange

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n N : ℕ)
variable (S : Scheme.{u}) (q : ℕ → ℕ)

instance boundedHilbertOver_hom_quasiCompact :
    QuasiCompact (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q).hom :=
  inferInstanceAs (QuasiCompact (Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S q ≫
    Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S))

instance boundedHilbertOver_hom_locallyOfFiniteType :
    LocallyOfFiniteType (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q).hom :=
  inferInstanceAs (LocallyOfFiniteType (Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S q ≫
    Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S))

instance boundedHilbertOver_hom_isSeparated :
    IsSeparated (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q).hom :=
  inferInstanceAs (IsSeparated (Data.GradedHilbert.boundedHilbertParameter (ι := ι) n N S q ≫
    Grassmannian.Gluing.grassmannianStructureMap (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.StructureProperties.GradedHilbert
