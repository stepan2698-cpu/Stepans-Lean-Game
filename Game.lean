import Game.Metadata
import Game.Implication.Cancellation

-- Here's what we'll put on the title screen
Title "Stepan's Lean Game"
Introduction
"
This is my draft of the Lean game which extends the natural number game up to
proving the Fundamental Theorem of Arithmetic.
"

Info ""

/-! Information to be displayed on the servers landing page. -/
Languages "en"
--CaptionShort "Game Template"
--CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
