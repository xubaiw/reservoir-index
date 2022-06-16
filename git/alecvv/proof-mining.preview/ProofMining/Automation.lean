


macro "autowt" : tactic => `(repeat constructor)

macro "autowf" : tactic => `((repeat (try (any_goals constructor))); all_goals assumption)
