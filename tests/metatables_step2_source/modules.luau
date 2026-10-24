local Parent = require("./parent")
local instance = Parent.new(12)
local mt = {__index = instance}
local child = setmetatable({}, mt)
print("module-chain", child:get(), child.get(child))
mt.__index = {x = 4}
print("module-replace", child.x, child.get == nil)
local copy = table.clone(child)
print("module-clone", copy ~= child, copy.x, copy.get == nil)
