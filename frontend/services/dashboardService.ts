import { ClassSummary, QuickStats, ClassData } from '../types';

const API_BASE_URL = 'http://localhost:5000/api';

export const dashboardService = {
  // Get all classes for dashboard
  async getClasses(): Promise<ClassSummary[]> {
    try {
      const response = await fetch(`${API_BASE_URL}/dashboard/classes`);
      if (!response.ok) {
        throw new Error(`HTTP error! status: ${response.status}`);
      }
      const data = await response.json();
      
      // Convert date strings to Date objects
      return data.map((classData: any) => ({
        ...classData,
        lastSession: classData.lastSession ? new Date(classData.lastSession) : null,
        createdAt: classData.createdAt ? new Date(classData.createdAt) : new Date(),
        updatedAt: classData.updatedAt ? new Date(classData.updatedAt) : new Date(),
      }));
    } catch (error) {
      console.error('Error fetching classes:', error);
      throw error;
    }
  },

  // Get dashboard stats
  async getStats(): Promise<QuickStats> {
    try {
      const response = await fetch(`${API_BASE_URL}/dashboard/stats`);
      if (!response.ok) {
        throw new Error(`HTTP error! status: ${response.status}`);
      }
      return await response.json();
    } catch (error) {
      console.error('Error fetching stats:', error);
      throw error;
    }
  },

  // Get detailed class data
  async getClassData(classId: string): Promise<ClassData> {
    try {
      const response = await fetch(`${API_BASE_URL}/dashboard/class/${classId}`);
      if (!response.ok) {
        throw new Error(`HTTP error! status: ${response.status}`);
      }
      const data = await response.json();
      
      // Convert date strings to Date objects
      return {
        ...data,
        lastSession: data.lastSession ? new Date(data.lastSession) : null,
      };
    } catch (error) {
      console.error('Error fetching class data:', error);
      throw error;
    }
  },

  // Update session data
  async updateSessionData(classId: string, knowledgeState: any): Promise<void> {
    try {
      const response = await fetch(`${API_BASE_URL}/dashboard/update_session`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          classId,
          knowledgeState,
        }),
      });
      
      if (!response.ok) {
        throw new Error(`HTTP error! status: ${response.status}`);
      }
    } catch (error) {
      console.error('Error updating session data:', error);
      throw error;
    }
  },
}; 