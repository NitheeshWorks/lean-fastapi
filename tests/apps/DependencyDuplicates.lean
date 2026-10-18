-- upstream: tests/test_dependency_duplicates.py
import LeanFastapi
open LeanFastapi

namespace Tests.DependencyDuplicates

def app := FastAPI.new

structure Item where
  data : String
  deriving Model

def duplicateDependency (item : Item) : Item := item

def dependency (item2 : Item) : Item := item2

def subDuplicateDependency (item : Item) (sub_item : Depends duplicateDependency) : List Item :=
  [item, sub_item]

@[post "/with-duplicates"]
def withDuplicates (item : Item) (item2 : Depends duplicateDependency) : Handler Json :=
  return json% [item, item2]

@[post "/no-duplicates"]
def noDuplicates (item : Item) (item2 : Depends dependency) : Handler Json :=
  return json% [item, item2]

@[post "/with-duplicates-sub"]
def noDuplicatesSub (item : Item) (sub_items : Depends subDuplicateDependency) : Handler Json :=
  return json% [item, sub_items]

end Tests.DependencyDuplicates
