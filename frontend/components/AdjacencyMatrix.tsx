import React from 'react';
import { GraphNode, Edge } from '../types';

interface AdjacencyMatrixProps {
    nodes: GraphNode[];
    edges: Edge[];
}

const AdjacencyMatrix: React.FC<AdjacencyMatrixProps> = ({ nodes, edges }) => {
    const matrix = React.useMemo(() => {
        const matrixMap = new Map<string, number>();
        edges.forEach(edge => {
            const key = `${edge.source}->${edge.target}`;
            matrixMap.set(key, edge.weight);
        });
        return matrixMap;
    }, [edges]);

    const getCellStyles = (weight: number) => {
        if (weight <= 0) {
            return { backgroundColor: 'transparent', color: '#64748b' }; // slate-500 for '0.0'
        }
        // Interpolate from slate-700 to a vibrant green for better visual representation of weight
        // slate-700 HSL: 222, 14%, 25%
        // green-400 HSL: 130, 50%, 60%
        const h = 222 - (222 - 130) * weight; // Hue from slate blue to green
        const s = 14 + (50 - 14) * weight;   // Saturation from low to high
        const l = 25 + (60 - 25) * weight;   // Lightness from dark to light
        
        const backgroundColor = `hsl(${h}, ${s}%, ${l}%)`;
        const color = l > 50 ? 'black' : 'white'; // Ensure text is readable on the background

        return { backgroundColor, color };
    };

    return (
        <div className="bg-slate-800 p-4 rounded-lg shadow-lg">
            <h2 className="text-xl font-semibold text-cyan-400 mb-3">Adjacency Matrix (Prerequisite Weights)</h2>
            <div className="overflow-x-auto">
                <table className="w-full text-sm text-left text-slate-300 border-separate" style={{ borderSpacing: '1px' }}>
                    <thead>
                        <tr>
                            <th className="sticky left-0 p-2 bg-slate-700 rounded-tl-lg z-10">From &#8595; To &#8594;</th>
                            {nodes.map(node => (
                                <th key={node.id} className="p-2 bg-slate-700 align-bottom h-28">
                                    <div className="transform -rotate-60 origin-bottom-left whitespace-nowrap text-xs pb-1">
                                        {node.label}
                                    </div>
                                </th>
                            ))}
                        </tr>
                    </thead>
                    <tbody>
                        {nodes.map((fromNode) => (
                            <tr key={fromNode.id}>
                                <td className="sticky left-0 p-2 font-semibold bg-slate-700 z-10 whitespace-nowrap rounded-l-lg">{fromNode.label}</td>
                                {nodes.map(toNode => {
                                    if (fromNode.id === toNode.id) {
                                        return (
                                            <td key={toNode.id} className="p-2 text-center bg-slate-700 text-slate-500">
                                                -
                                            </td>
                                        );
                                    }
                                    const weight = matrix.get(`${fromNode.id}->${toNode.id}`) || 0;
                                    const styles = getCellStyles(weight);
                                    
                                    return (
                                        <td key={toNode.id} className="p-2 text-center rounded-sm" style={styles}>
                                            {weight.toFixed(1)}
                                        </td>
                                    );
                                })}
                            </tr>
                        ))}
                    </tbody>
                </table>
            </div>
        </div>
    );
};

export default AdjacencyMatrix;
