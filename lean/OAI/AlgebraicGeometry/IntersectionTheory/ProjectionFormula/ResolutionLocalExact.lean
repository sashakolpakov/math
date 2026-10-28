import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ComplexDeterminantBaseChange
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension

/-! # Resolution Local Exact -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionLocalExact

noncomputable section

/-! A length-two projective resolution becomes a short exact sequence
under a flat extension which kills its resolved module. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (M : ModuleCat.{u} R) (P : ProjectiveResolution M)

theorem shortExact (hP : IsZero (P.complex.X 3))
    (hM : IsZero ((ProjectionFormula.Flat.Extension.baseChange R S).obj M)) :
    (ComplexDeterminantBaseChange.complex R S (P.complex.d 2 1).hom
      (P.complex.d 1 0).hom (ModuleCat.hom_ext_iff.mp (P.complex.d_comp_d 2 1 0))).ShortExact := by
  let F := ProjectionFormula.Flat.Extension.baseChange R S
  let Q := F.mapProjectiveResolution P
  have hz : IsZero (Q.complex.X 3) := F.map_isZero hP
  have hmono : Mono (Q.complex.d 2 1) := (Q.exact_succ 1).mono_g (hz.eq_of_src _ _)
  have hepi : Epi (Q.complex.d 1 0) := Q.exact₀.epi_f (hM.eq_of_tgt _ _)
  exact
    { exact := Q.exact_succ 0
      mono_f := hmono
      epi_g := hepi }

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResolutionLocalExact
