import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.AcyclicSheafSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnderlyingAdditiveSheafExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology

/-! # Acyclic Module Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.AcyclicModuleSections

noncomputable section

/-! The bounded acyclic-sheaf argument applies to actual module complexes
and their native global-section maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

theorem bounded_acyclic_moduleComplex_last_sections_surjective
    {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) (hK : K.Acyclic)
    (hH : ∀ i q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (K.X i) (q + 1)))
    (r : ℕ) (hbelow : ∀ i : ℤ, i < -(r : ℤ) → IsZero (K.X i))
    (habove : IsZero (K.X 1)) :
    Function.Surjective ((K.d (-1) 0).app (⊤ : X.Opens)) := by
  let F := UnderlyingAdditiveSheafExactness.ModuleSheaf.toSheaf X
  let C := (F.mapHomologicalComplex (.up ℤ)).obj K
  have hC : C.Acyclic := by
    intro i
    apply (C.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mpr
    change ((K.sc' (i - 1) i (i + 1)).map F).Exact
    exact ((K.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mp (hK i)).map F
  exact AcyclicSheafSections.NativeCech.bounded_acyclic_sheafComplex_last_sections_surjective C hC hH r
    (fun i hi => F.map_isZero (hbelow i hi)) (F.map_isZero habove)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.AcyclicModuleSections
