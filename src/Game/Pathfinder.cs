#region license

// Copyright (c) 2021, andreakarasho
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. All advertising materials mentioning features or use of this software
//    must display the following acknowledgement:
//    This product includes software developed by andreakarasho - https://github.com/andreakarasho
// 4. Neither the name of the copyright holder nor the
//    names of its contributors may be used to endorse or promote products
//    derived from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS ''AS IS'' AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#endregion

using System;
using System.Collections.Generic;
using System.Collections.Specialized;
using System.Linq;
using System.Xml.Linq;
using ClassicUO.Configuration;
using ClassicUO.Game.Data;
using ClassicUO.Game.GameObjects;
using ClassicUO.Game.Managers;
using ClassicUO.IO.Resources;
using Microsoft.Xna.Framework;
using MathHelper = ClassicUO.Utility.MathHelper;

namespace ClassicUO.Game
{
    internal static class Pathfinder
    {
        private const int PATHFINDER_MAX_NODES = 10000;
        private const int NodeMapSize = 1000;
        private static PathNode _goalNode;
        private static int _pathfindDistance;
        //private static readonly PathNode[] _openList = new PathNode[PATHFINDER_MAX_NODES];
        //private static readonly PathNode[] _closedList = new PathNode[PATHFINDER_MAX_NODES];
        private static Dictionary<Position, PathNode> _nodeMap;

        private static readonly PathNode[] _path = new PathNode[PATHFINDER_MAX_NODES];
        private static int _pointIndex, _pathSize;
        private static bool _run;
        private static readonly int[] _offsetX =
        {
            0, 1, 1, 1, 0, -1, -1, -1, 0, 1
        };
        private static readonly int[] _offsetY =
        {
            -1, -1, 0, 1, 1, 1, 0, -1, -1, -1
        };
        private static readonly sbyte[] _dirOffset =
        {
            1, -1
        };
        private static Point _startPoint, _endPoint;

        public static bool AutoWalking { get; set; }

        public static bool PathindingCanBeCancelled { get; set; }

        public static bool BlockMoving { get; set; }

        public static bool FastRotation { get; set; }


        private static bool CreateItemList(List<PathObject> list, int x, int y, int stepState)
        {
            GameObject tile = World.Map.GetTile(x, y, false);

            if (tile == null)
            {
                return false;
            }

            bool ignoreGameCharacters = ProfileManager.CurrentProfile.IgnoreStaminaCheck || stepState == (int) PATH_STEP_STATE.PSS_DEAD_OR_GM || World.Player.IgnoreCharacters || !(World.Player.Stamina < World.Player.StaminaMax && World.Map.Index == 0);

            bool isGM = World.Player.Graphic == 0x03DB;

            GameObject obj = tile;

            while (obj.TPrevious != null)
            {
                obj = obj.TPrevious;
            }

            for (; obj != null; obj = obj.TNext)
            {
                if (World.CustomHouseManager != null && obj.Z < World.Player.Z)
                {
                    continue;
                }

                ushort graphicHelper = obj.Graphic;

                switch (obj)
                {
                    case Land tile1:

                        if (graphicHelper < 0x01AE && graphicHelper != 2 || graphicHelper > 0x01B5 && graphicHelper != 0x01DB)
                        {
                            uint flags = (uint) PATH_OBJECT_FLAGS.POF_IMPASSABLE_OR_SURFACE;

                            if (stepState == (int) PATH_STEP_STATE.PSS_ON_SEA_HORSE)
                            {
                                if (tile1.TileData.IsWet)
                                {
                                    flags = (uint) (PATH_OBJECT_FLAGS.POF_IMPASSABLE_OR_SURFACE | PATH_OBJECT_FLAGS.POF_SURFACE | PATH_OBJECT_FLAGS.POF_BRIDGE);
                                }
                            }
                            else
                            {
                                if (!tile1.TileData.IsImpassable)
                                {
                                    flags = (uint) (PATH_OBJECT_FLAGS.POF_IMPASSABLE_OR_SURFACE | PATH_OBJECT_FLAGS.POF_SURFACE | PATH_OBJECT_FLAGS.POF_BRIDGE);
                                }

                                if (stepState == (int) PATH_STEP_STATE.PSS_FLYING && tile1.TileData.IsNoDiagonal)
                                {
                                    flags |= (uint) PATH_OBJECT_FLAGS.POF_NO_DIAGONAL;
                                }
                            }

                            int landMinZ = tile1.MinZ;
                            int landAverageZ = tile1.AverageZ;
                            int landHeight = landAverageZ - landMinZ;

                            list.Add
                            (
                                new PathObject
                                (
                                    flags,
                                    landMinZ,
                                    landAverageZ,
                                    landHeight,
                                    obj
                                )
                            );
                        }

                        break;

                    case GameEffect _: break;

                    default:
                        bool canBeAdd = true;
                        bool dropFlags = false;

                        switch (obj)
                        {
                            case Mobile mobile:
                                {
                                    if (!ignoreGameCharacters && !mobile.IsDead && !mobile.IgnoreCharacters)
                                    {
                                        list.Add
                                        (
                                            new PathObject
                                            (
                                            (uint) PATH_OBJECT_FLAGS.POF_IMPASSABLE_OR_SURFACE,
                                                mobile.Z,
                                                mobile.Z + Constants.DEFAULT_CHARACTER_HEIGHT,
                                                Constants.DEFAULT_CHARACTER_HEIGHT,
                                                mobile
                                            )
                                        );
                                    }

                                    canBeAdd = false;

                                    break;
                                }

                            case Item item when item.IsMulti || item.ItemData.IsInternal:
                                {
                                    canBeAdd = false;

                                    break;
                                }

                            case Item item2:
                                if (stepState == (int) PATH_STEP_STATE.PSS_DEAD_OR_GM && (item2.ItemData.IsDoor || item2.ItemData.Weight <= 0x5A || isGM && !item2.IsLocked))
                                {
                                    dropFlags = true;
                                }
                                else if (ProfileManager.CurrentProfile.SmoothDoors && item2.ItemData.IsDoor)
                                {
                                    dropFlags = true;
                                }
                                else
                                {
                                    dropFlags = graphicHelper >= 0x3946 && graphicHelper <= 0x3964 || graphicHelper == 0x0082;
                                }

                                break;

                            case Multi m:

                                if ((World.CustomHouseManager != null && m.IsCustom && (m.State & CUSTOM_HOUSE_MULTI_OBJECT_FLAGS.CHMOF_GENERIC_INTERNAL) == 0) || m.IsHousePreview)
                                {
                                    canBeAdd = false;
                                }

                                if ((m.State & CUSTOM_HOUSE_MULTI_OBJECT_FLAGS.CHMOF_IGNORE_IN_RENDER) != 0)
                                {
                                    dropFlags = true;
                                }

                                break;
                        }

                        if (canBeAdd)
                        {
                            uint flags = 0;

                            if (!(obj is Mobile))
                            {
                                ref StaticTiles itemdata = ref TileDataLoader.Instance.StaticData[obj.Graphic];

                                if (stepState == (int) PATH_STEP_STATE.PSS_ON_SEA_HORSE)
                                {
                                    if (itemdata.IsWet)
                                    {
                                        flags = (uint) (PATH_OBJECT_FLAGS.POF_SURFACE | PATH_OBJECT_FLAGS.POF_BRIDGE);
                                    }
                                }
                                else
                                {
                                    if (itemdata.IsImpassable || itemdata.IsSurface)
                                    {
                                        flags = (uint) PATH_OBJECT_FLAGS.POF_IMPASSABLE_OR_SURFACE;
                                    }

                                    if (!itemdata.IsImpassable)
                                    {
                                        if (itemdata.IsSurface)
                                        {
                                            flags |= (uint) PATH_OBJECT_FLAGS.POF_SURFACE;
                                        }

                                        if (itemdata.IsBridge)
                                        {
                                            flags |= (uint) PATH_OBJECT_FLAGS.POF_BRIDGE;
                                        }
                                    }

                                    if (stepState == (int) PATH_STEP_STATE.PSS_DEAD_OR_GM)
                                    {
                                        if (graphicHelper <= 0x0846)
                                        {
                                            if (!(graphicHelper != 0x0846 && graphicHelper != 0x0692 && (graphicHelper <= 0x06F4 || graphicHelper > 0x06F6)))
                                            {
                                                dropFlags = true;
                                            }
                                        }
                                        else if (graphicHelper == 0x0873)
                                        {
                                            dropFlags = true;
                                        }
                                    }

                                    if (dropFlags)
                                    {
                                        flags &= 0xFFFFFFFE;
                                    }

                                    if (stepState == (int) PATH_STEP_STATE.PSS_FLYING && itemdata.IsNoDiagonal)
                                    {
                                        flags |= (uint) PATH_OBJECT_FLAGS.POF_NO_DIAGONAL;
                                    }
                                }

                                if (flags != 0)
                                {
                                    int objZ = obj.Z;
                                    int staticHeight = itemdata.Height;
                                    int staticAverageZ = staticHeight;

                                    if (itemdata.IsBridge)
                                    {
                                        staticAverageZ /= 2;
                                        // revert fix from fwiffo because it causes unwalkable stairs [down --> up]
                                        //staticAverageZ += staticHeight % 2;
                                    }

                                    list.Add
                                    (
                                        new PathObject
                                        (
                                            flags,
                                            objZ,
                                            staticAverageZ + objZ,
                                            staticHeight,
                                            obj
                                        )
                                    );
                                }
                            }
                        }

                        break;
                }
            }

            return list.Count != 0;
        }

        private static int CalculateMinMaxZ
        (
            ref int minZ,
            ref int maxZ,
            int newX,
            int newY,
            int currentZ,
            int newDirection,
            int stepState
        )
        {
            minZ = -128;
            maxZ = currentZ;
            newDirection &= 7;
            int direction = newDirection ^ 4;
            newX += _offsetX[direction];
            newY += _offsetY[direction];
            List<PathObject> list = new List<PathObject>();

            if (!CreateItemList(list, newX, newY, stepState) || list.Count == 0)
            {
                return 0;
            }

            foreach (PathObject obj in list)
            {
                GameObject o = obj.Object;
                int averageZ = obj.AverageZ;

                if (averageZ <= currentZ && o is Land tile && tile.IsStretched)
                {
                    int avgZ = tile.CalculateCurrentAverageZ(newDirection);

                    if (minZ < avgZ)
                    {
                        minZ = avgZ;
                    }

                    if (maxZ < avgZ)
                    {
                        maxZ = avgZ;
                    }
                }
                else
                {
                    if ((obj.Flags & (uint) PATH_OBJECT_FLAGS.POF_IMPASSABLE_OR_SURFACE) != 0 && averageZ <= currentZ && minZ < averageZ)
                    {
                        minZ = averageZ;
                    }

                    if ((obj.Flags & (uint) PATH_OBJECT_FLAGS.POF_BRIDGE) != 0 && currentZ == averageZ)
                    {
                        int z = obj.Z;
                        int height = z + obj.Height;

                        if (maxZ < height)
                        {
                            maxZ = height;
                        }

                        if (minZ > z)
                        {
                            minZ = z;
                        }
                    }
                }
            }

            maxZ += 2;

            return maxZ;
        }

        public static bool CalculateNewZ(int x, int y, ref sbyte z, int direction)
        {
            int stepState = (int) PATH_STEP_STATE.PSS_NORMAL;

            if (World.Player.IsDead || World.Player.Graphic == 0x03DB)
            {
                stepState = (int) PATH_STEP_STATE.PSS_DEAD_OR_GM;
            }
            else
            {
                if (World.Player.IsGargoyle && World.Player.IsFlying)
                {
                    stepState = (int) PATH_STEP_STATE.PSS_FLYING;
                }
                else
                {
                    Item mount = World.Player.FindItemByLayer(Layer.Mount);

                    if (mount != null && mount.Graphic == 0x3EB3) // sea horse
                    {
                        stepState = (int) PATH_STEP_STATE.PSS_ON_SEA_HORSE;
                    }
                }
            }

            int minZ = -128;
            int maxZ = z;

            CalculateMinMaxZ
            (
                ref minZ,
                ref maxZ,
                x,
                y,
                z,
                direction,
                stepState
            );

            List<PathObject> list = new List<PathObject>();

            if (World.CustomHouseManager != null)
            {
                Rectangle rect = new Rectangle(World.CustomHouseManager.StartPos.X, World.CustomHouseManager.StartPos.Y, World.CustomHouseManager.EndPos.X, World.CustomHouseManager.EndPos.Y);

                if (!rect.Contains(x, y))
                {
                    return false;
                }
            }

            if (!CreateItemList(list, x, y, stepState) || list.Count == 0)
            {
                return false;
            }

            list.Sort();

            list.Add
            (
                new PathObject
                (
                    (uint) PATH_OBJECT_FLAGS.POF_IMPASSABLE_OR_SURFACE,
                    128,
                    128,
                    128,
                    null
                )
            );

            int resultZ = -128;

            if (z < minZ)
            {
                z = (sbyte) minZ;
            }

            int currentTempObjZ = 1000000;
            int currentZ = -128;

            for (int i = 0; i < list.Count; i++)
            {
                PathObject obj = list[i];

                if ((obj.Flags & (uint) PATH_OBJECT_FLAGS.POF_NO_DIAGONAL) != 0 && stepState == (int) PATH_STEP_STATE.PSS_FLYING)
                {
                    int objAverageZ = obj.AverageZ;
                    int delta = Math.Abs(objAverageZ - z);

                    if (delta <= 25)
                    {
                        resultZ = objAverageZ != -128 ? objAverageZ : currentZ;

                        break;
                    }
                }

                if ((obj.Flags & (uint) PATH_OBJECT_FLAGS.POF_IMPASSABLE_OR_SURFACE) != 0)
                {
                    int objZ = obj.Z;

                    if (objZ - minZ >= Constants.DEFAULT_BLOCK_HEIGHT)
                    {
                        for (int j = i - 1; j >= 0; j--)
                        {
                            PathObject tempObj = list[j];

                            if ((tempObj.Flags & (uint) (PATH_OBJECT_FLAGS.POF_SURFACE | PATH_OBJECT_FLAGS.POF_BRIDGE)) != 0)
                            {
                                int tempAverageZ = tempObj.AverageZ;

                                if (tempAverageZ >= currentZ && objZ - tempAverageZ >= Constants.DEFAULT_BLOCK_HEIGHT && (tempAverageZ <= maxZ && (tempObj.Flags & (uint) PATH_OBJECT_FLAGS.POF_SURFACE) != 0 || (tempObj.Flags & (uint) PATH_OBJECT_FLAGS.POF_BRIDGE) != 0 && tempObj.Z <= maxZ))
                                {
                                    int delta = Math.Abs(z - tempAverageZ);

                                    if (delta < currentTempObjZ)
                                    {
                                        currentTempObjZ = delta;
                                        resultZ = tempAverageZ;
                                    }
                                }
                            }
                        }
                    }

                    int averageZ = obj.AverageZ;

                    if (minZ < averageZ)
                    {
                        minZ = averageZ;
                    }

                    if (currentZ < averageZ)
                    {
                        currentZ = averageZ;
                    }
                }
            }

            z = (sbyte) resultZ;

            return resultZ != -128;
        }

        public static void GetNewXY(byte direction, ref int x, ref int y)
        {
            switch (direction & 7)
            {
                case 0:

                    {
                        y--;

                        break;
                    }

                case 1:

                    {
                        x++;
                        y--;

                        break;
                    }

                case 2:

                    {
                        x++;

                        break;
                    }

                case 3:

                    {
                        x++;
                        y++;

                        break;
                    }

                case 4:

                    {
                        y++;

                        break;
                    }

                case 5:

                    {
                        x--;
                        y++;

                        break;
                    }

                case 6:

                    {
                        x--;

                        break;
                    }

                case 7:

                    {
                        x--;
                        y--;

                        break;
                    }
            }
        }

        public static bool CanWalk(ref Direction direction, ref int x, ref int y, ref sbyte z)
        {
            int newX = x;
            int newY = y;
            sbyte newZ = z;
            byte newDirection = (byte) direction;
            GetNewXY((byte) direction, ref newX, ref newY);
            bool passed = CalculateNewZ(newX, newY, ref newZ, (byte) direction);

            if ((sbyte) direction % 2 != 0)
            {
                if (passed)
                {
                    for (int i = 0; i < 2 && passed; i++)
                    {
                        int testX = x;
                        int testY = y;
                        sbyte testZ = z;
                        byte testDir = (byte) (((byte) direction + _dirOffset[i]) % 8);
                        GetNewXY(testDir, ref testX, ref testY);
                        passed = CalculateNewZ(testX, testY, ref testZ, testDir);
                    }
                }

                if (!passed)
                {
                    for (int i = 0; i < 2 && !passed; i++)
                    {
                        newX = x;
                        newY = y;
                        newZ = z;
                        newDirection = (byte) (((byte) direction + _dirOffset[i]) % 8);
                        GetNewXY(newDirection, ref newX, ref newY);
                        passed = CalculateNewZ(newX, newY, ref newZ, newDirection);
                    }
                }
            }

            if (passed)
            {
                x = newX;
                y = newY;
                z = newZ;
                direction = (Direction) newDirection;
            }

            return passed;
        }

        private static int GetGoalDistCost(Point point, int cost)
        {
            return Math.Max(Math.Abs(_endPoint.X - point.X), Math.Abs(_endPoint.Y - point.Y));
        }

        private static PathNode OpenNode(int direction, Position openPosition, PathNode parent, int cost)
        {
            PathNode node = GetPathNode(openPosition);

            if (node == null)
            {
                Point position = new Point(openPosition.X, openPosition.Y);
                var goalCost = GetGoalDistCost(position, cost);
                var startCost = parent.DistFromStartCost + cost;
                node = AddNode(new PathNode(openPosition)
                {
                    Parent = parent,
                    Direction = direction,
                    DistFromGoalCost = goalCost,
                    DistFromStartCost = startCost,
                    Cost = goalCost + startCost,
                });

                if (MathHelper.GetDistance(_endPoint, position) <= _pathfindDistance)
                    _goalNode = node;
            }
            else if (!node.Visited)
            {
                int startCost = parent.DistFromStartCost + cost;

                if (node.DistFromStartCost > startCost)
                {
                    node.Parent = parent;
                    node.Direction = direction;
                    node.DistFromStartCost = startCost + cost;
                    node.Cost = node.DistFromGoalCost + node.DistFromStartCost;
                }
            }


            return node;
        }

        private static PathNode AddNode(PathNode pathNode)
        {
            _nodeMap.Add(pathNode.Position, pathNode);

            return pathNode;
        }

        private static PathNode GetPathNode(Position openPosition) 
            => _nodeMap.TryGetValue(openPosition, out var node) ? node : null;

        private static void OpenNodes(PathNode node)
        {
            for (int i = 0; i < 8; i++)
            {
                Direction direction = (Direction)i;
                int x = node.X;
                int y = node.Y;
                sbyte z = (sbyte)node.Z;
                Direction oldDirection = direction;

                if (CanWalk(ref direction, ref x, ref y, ref z) && direction == oldDirection)
                {

                    int diagonal = i % 2;
                    if (diagonal != 0)
                    {
                        Direction wantDirection = (Direction)i;
                        int wantX = node.X;
                        int wantY = node.Y;
                        GetNewXY((byte)wantDirection, ref wantX, ref wantY);

                        if (x != wantX || y != wantY)
                        {
                            diagonal = -1;
                        }
                    }


                    if (diagonal >= 0)
                        OpenNode(
                        (int)direction,
                        new Position(
                        x,
                        y,
                        z),
                        node,
                        diagonal == 0 ? 1 : 2);
                }
            }
        }

        private static PathNode FindCheapestNode()
        {
            PathNode cheapestNode = _nodeMap.Values.Where(x => !x.Visited).Min();

            if (cheapestNode != null)
                cheapestNode.Visited = true;

            return cheapestNode;
        }

        private static bool FindPath(int maxNodes)
        {
            var goalCost = GetGoalDistCost(_startPoint, 0);
            var currentNode = new PathNode(_startPoint.X, _startPoint.Y, World.Player.Z)
            {
                Visited = true,
                Parent = null,
                DistFromGoalCost = goalCost,
                Cost = goalCost,
            };

            if (GetGoalDistCost(_startPoint, 0) > 14)
            {
                _run = true;
            }

            while (AutoWalking)
            {
                OpenNodes(currentNode);

                if (_goalNode!=null)
                {
                    int totalNodes = 0;
                    PathNode goalNode = _goalNode;

                    while (goalNode.Parent != null && goalNode != goalNode.Parent)
                    {
                        goalNode = goalNode.Parent;
                        totalNodes++;
                    }

                    totalNodes++;
                    _pathSize = totalNodes;
                    goalNode = _goalNode;

                    while (totalNodes != 0)
                    {
                        totalNodes--;
                        _path[totalNodes] = goalNode;
                        goalNode = goalNode.Parent;
                    }

                    break;
                }

                currentNode = FindCheapestNode();

                if (currentNode == null || _nodeMap.Count >= maxNodes)
                {
                    return false;
                }
            }

            return true;
        }

        public static bool WalkTo(int x, int y, int z, int distance)
        {
            if (World.Player == null /*|| World.Player.Stamina == 0*/ || World.Player.IsParalyzed)
            {
                return false;
            }

            _nodeMap = new Dictionary<Position, PathNode>(PATHFINDER_MAX_NODES);


            int playerX = World.Player.X;
            int playerY = World.Player.Y;
            //sbyte playerZ = 0;
            //Direction playerDir = Direction.None;

            //World.Player.GetEndPosition(ref playerX, ref playerY, ref playerZ, ref playerDir);
            _startPoint.X = playerX;
            _startPoint.Y = playerY;
            _endPoint.X = x;
            _endPoint.Y = y;
            _goalNode = null;
            _pathfindDistance = distance;
            _pathSize = 0;
            PathindingCanBeCancelled = true;
            StopAutoWalk();
            AutoWalking = true;

            if (FindPath(PATHFINDER_MAX_NODES))
            {
                _pointIndex = 1;
                ProcessAutoWalk();
            }
            else
            {
                AutoWalking = false;
            }

            _nodeMap = null;
            return _pathSize != 0;
        }

        public static void ProcessAutoWalk()
        {
            if (AutoWalking && World.InGame && World.Player.Walker.StepsCount < Constants.MAX_STEP_COUNT && World.Player.Walker.LastStepRequestTime <= Time.Ticks)
            {
                if (_pointIndex >= 0 && _pointIndex < _pathSize)
                {
                    PathNode p = _path[_pointIndex];

                    World.Player.GetEndPosition(out int x, out int y, out sbyte z, out Direction dir);

                    if (dir == (Direction) p.Direction)
                    {
                        _pointIndex++;
                    }

                    if (!World.Player.Walk((Direction) p.Direction, _run))
                    {
                        StopAutoWalk();
                    }
                }
                else
                {
                    StopAutoWalk();
                }
            }
        }

        public static void StopAutoWalk()
        {
            AutoWalking = false;
            _run = false;
            _pathSize = 0;
        }

        private enum PATH_STEP_STATE
        {
            PSS_NORMAL = 0,
            PSS_DEAD_OR_GM,
            PSS_ON_SEA_HORSE,
            PSS_FLYING
        }

        [Flags]
        private enum PATH_OBJECT_FLAGS : uint
        {
            POF_IMPASSABLE_OR_SURFACE = 0x00000001,
            POF_SURFACE = 0x00000002,
            POF_BRIDGE = 0x00000004,
            POF_NO_DIAGONAL = 0x00000008
        }

        private class PathObject : IComparable<PathObject>
        {
            public PathObject(uint flags, int z, int avgZ, int h, GameObject obj)
            {
                Flags = flags;
                Z = z;
                AverageZ = avgZ;
                Height = h;
                Object = obj;
            }

            public uint Flags { get; }

            public int Z { get; }

            public int AverageZ { get; }

            public int Height { get; }

            public GameObject Object { get; }

            public int CompareTo(PathObject other)
            {
                int comparision = Z - other.Z;

                if (comparision == 0)
                {
                    comparision = Height - other.Height;
                }

                return comparision;
            }
        }

        private readonly struct Position
        {
            public Position(int x, int y, int z)
            {
                X = x;
                Y = y;
                Z = z;
            }

            public int X { get; }

            public int Y { get; }

            public int Z { get; }

            public override bool Equals(object obj)
                => Equals(obj as PathNode);

            private bool Equals(PathNode obj) => obj != null && X == obj.X && Y == obj.Y && Z == obj.Z;

            //public override int GetHashCode()
            //{
            //    unchecked
            //    {
            //        int hashCode = X;
            //        hashCode = (hashCode * 397) ^ Y;
            //        hashCode = (hashCode * 397) ^ Z;

            //        return hashCode;
            //    }
            //}
            // or a faster one
            public override int GetHashCode()
            {
                unchecked
                {
                    return X + Y + Z;
                }
            }

        }
        private class PathNode : IComparable<PathNode>
        {
            public PathNode(int x, int y, int z) 
                : this(new Position(x, y, z))
            {
            }

            public PathNode(Position position)
            {
                Position = position;
            }

            public Position Position { get; }
            public int X => Position.X;

            public int Y => Position.Y;

            public int Z => Position.Z;

            public int Direction { get; set; }

            public bool Visited { get; set; }

            public int Cost { get; set; }

            public int DistFromStartCost { get; set; }

            public int DistFromGoalCost { get; set; }

            public PathNode Parent { get; set; }


            public int CompareTo(PathNode other) 
                => Cost.CompareTo(other.Cost);
        }
    }
}