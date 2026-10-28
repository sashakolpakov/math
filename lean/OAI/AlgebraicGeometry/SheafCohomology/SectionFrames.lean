import OAI.AlgebraicGeometry.SheafCohomology.TensorCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame

/-! # Section Frames -/

namespace OAI.AlgebraicGeometry.SheafCohomology.SectionFrames.Projective

noncomputable section

/-! Realizing natural ambient section frames as isomorphisms on the open slice site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
def sectionFrameOver (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules)
    (U : A.carrier.Opens)
    (e : ∀ (V : A.carrier.Opens), V ≤ U →
      Γ(M, V) ≃ₗ[Γ(A.carrier, V)] Γ(A.carrier, V))
    (he : ∀ {V W : A.carrier.Opens} (hVW : V ≤ W) (hWU : W ≤ U) (m : Γ(M, W)),
      e V (hVW.trans hWU) (M.presheaf.map (homOfLE hVW).op m) =
        A.carrier.presheaf.map (homOfLE hVW).op (e W hWU m)) :
    M.over U ≅ SheafOfModules.unit (A.carrier.ringCatSheaf.over U) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk
    (fun V => (e V.unop.left (leOfHom V.unop.hom)).toModuleIso) ?_
  intro V W f
  ext m
  exact he (leOfHom f.unop.left) (leOfHom V.unop.hom) m

/-- ChernClass's chosen ambient section coordinates give an actual slice-site frame. -/
def chosenSectionFrameOver (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A)
    (x : A.carrier) (U : A.carrier.Opens) (hU : U ≤ L.trivializingOpen x) :
    L.sheaf.over U ≅ SheafOfModules.unit (A.carrier.ringCatSheaf.over U) :=
  sectionFrameOver A L.sheaf U
    (fun V hV => L.sectionFrame x V (hV.trans hU))
    (fun hVW hWU => L.sectionFrame_naturality x hVW (hWU.trans hU))

set_option backward.isDefEq.respectTransparency false in
theorem chosenSectionFrameOver_apply (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A)
    (x : A.carrier) (U : A.carrier.Opens) (hU : U ≤ L.trivializingOpen x)
    (V : Over U) (m : Γ(L.sheaf, V.left)) :
    (chosenSectionFrameOver A L x U hU).hom.val.app (Opposite.op V) m =
      L.sectionFrame x V.left ((leOfHom V.hom).trans hU) m := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.SectionFrames.Projective
