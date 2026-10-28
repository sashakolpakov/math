import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorRefinementCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinementCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.RefinementConeOneCoordinates

/-! # Functor Refinement One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorRefinementOne.SectionFunctorRefinementHOne

noncomputable section

/-! H-one refinement and cone/comparison naturality in explicitly
composed section-functor coordinates, before native specialization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v a b c d e f g h
variable (R : Type u) [CommRing R]
  {A : Type a} [Category.{b} A] [Preadditive A]
  {C : Type c} [Category.{d} C] [HasBinaryProducts C]
  {D : Type e} [Category.{f} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {E : Type g} [Category.{h} E]
  (S : A ⥤ (Eᵒᵖ ⥤ ModuleCat.{max u v} R)) [S.Additive] (K : CochainComplex A ℕ)
  (G : C ⥤ D) (F : D ⥤ E) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) G]
  (r : FormalCoproduct.mk ι (G.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

def mapHOne :
    ((CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex V (FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates.oldSections S K F)).total (.up ℕ)).homology 1 ⟶
      ((CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates.newSections S K G F)).total (.up ℕ)).homology 1 :=
  HomologicalComplex.homologyMap (FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates.refinement S K G F U V r) 1

variable (P : Dᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ)
  (φ : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P ⟶ FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates.oldSections S K F)
  (ψ : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (G.op ⋙ P) ⟶ FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates.newSections S K G F)
  (hφ : ∀ q, q ≤ 1 → ∀ W,
    ((((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback G).mapHomologicalComplex (.up ℕ)).map φ).f q).app W =
      (ψ.f q).app W)

include hφ in
theorem comparison : CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R V φ ≫ mapHOne R S K G F U V r =
    CechAssembly.RefinementCohomology.CechAssemblyRefinementHOne.mapHOne R G U V r P ≫
      CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U ψ :=
  CechAssembly.RefinementCohomology.CechAssemblyRefinementHOne.comparison R G U V r P φ ψ hφ

def pulled : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (G.op ⋙ P) ⟶
    FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates.newSections S K G F :=
  ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback G).mapHomologicalComplex (.up ℕ)).map φ

def pulledHOne := CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U (pulled R S K G F P φ)

theorem naturality : CechPresheaf.RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R V φ ≫ mapHOne R S K G F U V r =
    CechAssembly.RefinementCohomology.CechAssemblyRefinementHOne.mapHOne R G U V r P ≫
      pulledHOne R S K G F U P φ :=
  comparison R S K G F U V r P φ (pulled R S K G F P φ) (fun _ _ _ => rfl)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorRefinementOne.SectionFunctorRefinementHOne
